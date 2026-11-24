import { defineRule } from '@oxlint/plugins'

import {
  allowlistProperties,
  readBooleanOption,
  readOptionObject,
  reportAllowed,
} from '../lib/allowlist.ts'
import { containsNode } from '../lib/ast-search.ts'
import { isTestSupportFile } from '../lib/test-file.ts'

import type { ESTree } from '@oxlint/plugins'

const spyMatchers =
  /^(?:toHaveBeenCalled|toHaveBeenCalledOnce|toHaveBeenCalledTimes|toHaveBeenCalledWith|toHaveBeenCalledExactlyOnceWith|toHaveBeenLastCalledWith|toHaveBeenNthCalledWith|toHaveReturned|toHaveReturnedTimes|toHaveReturnedWith|toHaveLastReturnedWith|toHaveNthReturnedWith|toHaveResolved|toHaveResolvedTimes|toHaveResolvedWith|toHaveLastResolvedWith|toHaveNthResolvedWith)$/u

const clockCall = /^now(?:[A-Z_]|$)/u

type Loop = ESTree.WhileStatement | ESTree.DoWhileStatement | ESTree.ForStatement

function propertyName(node: ESTree.MemberExpression) {
  return node.property.type === 'Identifier' && !node.computed ? node.property.name : undefined
}

function isCall(node: ESTree.Node, object: string, property: string) {
  return (
    node.type === 'MemberExpression' &&
    node.object.type === 'Identifier' &&
    node.object.name === object &&
    propertyName(node) === property
  )
}

const path: (node: ESTree.Node) => string[] | null = (node) => {
  if (node.type === 'ChainExpression') return path(node.expression)

  if (node.type === 'Identifier') return [node.name]

  if (node.type !== 'MemberExpression') return null

  const object = path(node.object)

  return object && [...object, propertyName(node) ?? '[]']
}

function readsRecorder(node: ESTree.Node) {
  const names = path(node)

  if (!names || names.includes('current')) return false

  const last = names.at(-1)

  return names.includes('mock') || (names.length > 1 && (last === 'length' || last === 'size'))
}

function polledValue(callback: ESTree.Node) {
  if (callback.type !== 'ArrowFunctionExpression' && callback.type !== 'FunctionExpression') {
    return null
  }

  if (!callback.body) return null

  if (callback.body.type !== 'BlockStatement') return callback.body

  const [statement, ...rest] = callback.body.body

  if (rest.length > 0) return null

  if (statement?.type === 'ReturnStatement') return statement.argument

  return statement?.type === 'ExpressionStatement' ? statement.expression : null
}

function assertsRecorder(node: ESTree.Node) {
  if (node.type !== 'CallExpression' || node.callee.type !== 'MemberExpression') return false

  const matcher = propertyName(node.callee) ?? ''
  const subject =
    node.callee.object.type === 'MemberExpression' && propertyName(node.callee.object) === 'not'
      ? node.callee.object.object
      : node.callee.object

  if (
    subject.type !== 'CallExpression' ||
    subject.callee.type !== 'Identifier' ||
    subject.callee.name !== 'expect'
  ) {
    return false
  }

  const [target] = subject.arguments

  if (!target || target.type === 'SpreadElement') return false

  if (readsRecorder(target)) return true

  const names = path(target)

  return (
    names !== null &&
    !names.includes('current') &&
    (spyMatchers.test(matcher) || matcher === 'toHaveLength')
  )
}

function pollsLength(node: ESTree.CallExpression, value: ESTree.Node) {
  const parent =
    node.parent.type === 'MemberExpression' && propertyName(node.parent) === 'not'
      ? node.parent.parent
      : node.parent
  const names = path(value)
  const matcher = parent.type === 'MemberExpression' ? (propertyName(parent) ?? '') : ''

  return (
    (matcher === 'toHaveLength' || spyMatchers.test(matcher)) &&
    names !== null &&
    !names.includes('current')
  )
}

function conditionReadsRecorder(node: ESTree.Node) {
  const pending: ESTree.Node[] = [node]

  while (pending.length > 0) {
    const current = pending.pop()

    if (current === undefined) break

    if (readsRecorder(current)) return true

    if (current.type === 'BinaryExpression' || current.type === 'LogicalExpression') {
      pending.push(current.left, current.right)
    } else if (current.type === 'UnaryExpression') {
      pending.push(current.argument)
    } else if (current.type === 'SequenceExpression') {
      pending.push(...current.expressions)
    }
  }

  return false
}

function isFunction(node: ESTree.Node) {
  return (
    node.type === 'ArrowFunctionExpression' ||
    node.type === 'FunctionExpression' ||
    node.type === 'FunctionDeclaration'
  )
}

function enclosedBy(node: ESTree.Node, root: ESTree.Node) {
  for (
    let current: ESTree.Node | null = node.parent;
    current && current !== root;
    current = current.parent
  ) {
    if (isFunction(current)) return false
  }

  return true
}

function within(root: ESTree.Node, predicate: (node: ESTree.Node) => boolean) {
  return containsNode(root, (node) => predicate(node) && enclosedBy(node, root))
}

function readsClock(node: ESTree.Node) {
  if (node.type === 'NewExpression') {
    return (
      node.callee.type === 'Identifier' &&
      node.callee.name === 'Date' &&
      node.arguments.length === 0
    )
  }

  if (node.type !== 'CallExpression') return false

  const { callee } = node

  if (callee.type === 'Identifier') return clockCall.test(callee.name)

  return callee.type === 'MemberExpression' && propertyName(callee) === 'now'
}

function checksDeadline(body: ESTree.Node) {
  return within(
    body,
    (node) =>
      (node.type === 'IfStatement' || node.type === 'ConditionalExpression') &&
      within(node.test, readsClock),
  )
}

function clockLoop(node: Loop) {
  const clocked = (node.test !== null && within(node.test, readsClock)) || checksDeadline(node.body)

  return clocked && within(node.body, (child) => child.type === 'AwaitExpression')
}

export const noUnsignaledPoll = defineRule({
  meta: {
    type: 'problem',
    schema: [
      {
        type: 'object',
        properties: {
          ...allowlistProperties,
          checkClockLoops: { type: 'boolean' },
        },
        additionalProperties: false,
      },
    ],
    docs: {
      description:
        'Disallow polling spy/request-recorder state or clock-deadline loops in tests; await a real signal instead.',
    },
    messages: {
      poll: 'Await a signal instead of polling a spy or recorder: resolve a Promise.withResolvers() deferred from the handler or await the operation directly.',
      clock:
        'Await a signal instead of looping until a clock deadline: resolve a Promise.withResolvers() deferred or subscribe to the completion event.',
      stale:
        'This file now has {{count}} unsignaled polls; lower its bytewave/no-unsignaled-poll allowlist entry for {{path}} in oxlint.config.ts to {{count}}, or remove the entry at 0.',
    },
  },
  create(context) {
    const options = readOptionObject(context)
    const checkClockLoops = readBooleanOption(options, 'checkClockLoops') ?? true
    const violations: ESTree.Node[] = []
    const loops = new Set<ESTree.Node>()
    const support = isTestSupportFile(context.physicalFilename)

    function loop(node: Loop) {
      if (checkClockLoops && support && clockLoop(node)) {
        violations.push(node)
        loops.add(node)
      }
    }

    return {
      WhileStatement: loop,
      DoWhileStatement: loop,
      ForStatement: loop,
      CallExpression(node) {
        const poll = isCall(node.callee, 'expect', 'poll')
        const waitUntil = isCall(node.callee, 'vi', 'waitUntil')

        if (!poll && !waitUntil && !isCall(node.callee, 'vi', 'waitFor')) return

        const [callback] = node.arguments
        const value = callback && polledValue(callback)

        if (!value) return

        let unsignaled = readsRecorder(value)

        if (!unsignaled) {
          if (poll) {
            unsignaled = pollsLength(node, value)
          } else if (waitUntil) {
            unsignaled = conditionReadsRecorder(value)
          } else {
            unsignaled = assertsRecorder(value)
          }
        }

        if (unsignaled) violations.push(node)
      },
      'Program:exit'(program) {
        reportAllowed(context, program, violations, 'poll', undefined, (node) =>
          loops.has(node) ? 'clock' : 'poll',
        )
      },
    }
  },
})
