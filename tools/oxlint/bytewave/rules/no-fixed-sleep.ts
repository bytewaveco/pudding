import { defineRule } from '@oxlint/plugins'

import {
  allowlistProperties,
  readOptionObject,
  readStringArrayOption,
  reportAllowed,
} from '../lib/allowlist.ts'

import type { ESTree, Scope, SourceCode } from '@oxlint/plugins'

const defaultRunNow = ['act', 'waitFor', 'then', 'catch', 'finally', 'step']
const testCallees = new Set(['test', 'it', 'beforeEach', 'afterEach', 'beforeAll', 'afterAll'])
const timerModules = new Set(['node:timers/promises', 'timers/promises'])
const idleStates = new Set(['networkidle', 'networkidle0', 'networkidle2'])

type TimerBinding = 'setTimeout' | 'scheduler' | 'namespace'

function timerProperty(node: ESTree.MemberExpression) {
  if (!node.computed && node.property.type === 'Identifier') return node.property.name

  if (node.computed && node.property.type === 'Literal') return node.property.value

  return null
}

const timerBinding: (source: SourceCode, node: ESTree.Node) => TimerBinding | undefined = (
  source,
  node,
) => {
  if (node.type === 'MemberExpression') {
    const property = timerProperty(node)
    const object = timerBinding(source, node.object)

    if (object === 'namespace') {
      return property === 'setTimeout' || property === 'scheduler' ? property : undefined
    }

    return object === 'scheduler' && property === 'wait' ? 'setTimeout' : undefined
  }

  if (node.type !== 'Identifier') return undefined

  for (let scope: Scope | null = source.getScope(node); scope !== null; scope = scope.upper) {
    const definition = scope.set.get(node.name)?.defs[0]

    if (!definition) continue

    const { node: importedNode, parent } = definition

    if (parent?.type !== 'ImportDeclaration' || !timerModules.has(parent.source.value)) {
      return undefined
    }

    if (importedNode.type === 'ImportSpecifier') {
      const imported =
        importedNode.imported.type === 'Identifier'
          ? importedNode.imported.name
          : importedNode.imported.value

      return imported === 'setTimeout' || imported === 'scheduler' ? imported : undefined
    }

    return importedNode.type === 'ImportNamespaceSpecifier' ||
      importedNode.type === 'ImportDefaultSpecifier'
      ? 'namespace'
      : undefined
  }

  return node.name === 'scheduler' ? 'scheduler' : undefined
}

function isMember(node: ESTree.Node, object: string, property: string) {
  return (
    node.type === 'MemberExpression' &&
    node.object.type === 'Identifier' &&
    node.object.name === object &&
    node.property.type === 'Identifier' &&
    !node.computed &&
    node.property.name === property
  )
}

function isSetTimeout(node: ESTree.Node) {
  return (
    (node.type === 'Identifier' && node.name === 'setTimeout') ||
    isMember(node, 'globalThis', 'setTimeout') ||
    isMember(node, 'window', 'setTimeout')
  )
}

const calleeRoot: (node: ESTree.Node) => string | undefined = (node) => {
  if (node.type === 'CallExpression') return calleeRoot(node.callee)

  if (node.type === 'MemberExpression') return calleeRoot(node.object)

  if (node.type === 'TaggedTemplateExpression') return calleeRoot(node.tag)

  return node.type === 'Identifier' ? node.name : undefined
}

function calleeName(node: ESTree.Node) {
  if (node.type === 'Identifier') return node.name

  return node.type === 'MemberExpression' && !node.computed && node.property.type === 'Identifier'
    ? node.property.name
    : undefined
}

const inTestBody: (node: ESTree.Node, runNow: ReadonlySet<string>) => boolean = (node, runNow) => {
  let current: ESTree.Node | null = node.parent

  while (
    current &&
    current.type !== 'ArrowFunctionExpression' &&
    current.type !== 'FunctionExpression' &&
    current.type !== 'FunctionDeclaration'
  ) {
    current = current.parent
  }

  const call = current?.parent

  if (call?.type !== 'CallExpression') return false

  if (testCallees.has(calleeRoot(call.callee) ?? '')) return true

  return runNow.has(calleeName(call.callee) ?? '') && inTestBody(call, runNow)
}

function scheduled(body: ESTree.Node | null) {
  if (body?.type !== 'BlockStatement') return body

  const [statement, ...rest] = body.body

  return statement?.type === 'ExpressionStatement' && rest.length === 0
    ? statement.expression
    : null
}

function resolvesAfterTimeout(node: ESTree.NewExpression) {
  const [executor] = node.arguments

  if (
    !executor ||
    (executor.type !== 'ArrowFunctionExpression' && executor.type !== 'FunctionExpression')
  ) {
    return false
  }

  const [resolve] = executor.params

  if (resolve?.type !== 'Identifier') return false

  const call = scheduled(executor.body)

  if (call?.type !== 'CallExpression' || !isSetTimeout(call.callee)) return false

  const [handler] = call.arguments

  if (handler?.type === 'Identifier') return handler.name === resolve.name

  if (handler?.type !== 'ArrowFunctionExpression' && handler?.type !== 'FunctionExpression') {
    return false
  }

  const settle = scheduled(handler.body)

  return (
    settle?.type === 'CallExpression' &&
    settle.callee.type === 'Identifier' &&
    settle.callee.name === resolve.name
  )
}

function isIdleState(node: ESTree.Node | undefined) {
  return node?.type === 'Literal' && idleStates.has(String(node.value))
}

function isTimedWait(node: ESTree.CallExpression) {
  const { callee } = node

  if (
    callee.type !== 'MemberExpression' ||
    callee.computed ||
    callee.property.type !== 'Identifier'
  ) {
    return false
  }

  const [state] = node.arguments

  return (
    callee.property.name === 'waitForTimeout' ||
    (callee.property.name === 'waitForLoadState' && isIdleState(state))
  )
}

function waitsUntilIdle(node: ESTree.Node) {
  return (
    node.type === 'Property' &&
    !node.computed &&
    node.key.type === 'Identifier' &&
    node.key.name === 'waitUntil' &&
    isIdleState(node.value)
  )
}

function returned(node: ESTree.Node | null | undefined) {
  if (
    node?.type !== 'ArrowFunctionExpression' &&
    node?.type !== 'FunctionExpression' &&
    node?.type !== 'FunctionDeclaration'
  ) {
    return null
  }

  const { body } = node

  if (body?.type !== 'BlockStatement') return body ?? null

  const last = body.body.at(-1)

  return last?.type === 'ReturnStatement' ? last.argument : null
}

export const noFixedSleep = defineRule({
  meta: {
    type: 'problem',
    schema: [
      {
        type: 'object',
        properties: {
          ...allowlistProperties,
          runNow: { type: 'array', items: { type: 'string' } },
        },
        additionalProperties: false,
      },
    ],
    docs: {
      description:
        'Disallow awaiting a fixed real-time sleep in a test or hook body, and Playwright timed waits anywhere.',
    },
    messages: {
      sleep:
        'Replace this fixed sleep with a real signal: await the operation, Vue nextTick(), or a Promise.withResolvers() deferred resolved by the event. To move time, use fake timers (vi.useFakeTimers()).',
      timedWait:
        'Replace this timed Playwright wait with the state you need: a web-first assertion (await expect(locator).toBeVisible()), page.waitForResponse, page.waitForEvent, or page.waitForFunction.',
      stale:
        'This file now has {{count}} fixed sleeps; lower its bytewave/no-fixed-sleep allowlist entry for {{path}} in oxlint.config.ts to {{count}}, or remove the entry at 0.',
    },
  },
  create(context) {
    const options = readOptionObject(context)
    const runNow = new Set(readStringArrayOption(options, 'runNow') ?? defaultRunNow)
    const sleeps: ESTree.Node[] = []
    const timedWaits: ESTree.Node[] = []
    const helpers = new Map<string, ESTree.Node>()
    const helperCalls: [ESTree.Node, string][] = []
    let fakeTimers = false

    function recordHelper(name: string, node: ESTree.Node | null | undefined) {
      const value = returned(node)

      if (value) helpers.set(name, value)
    }

    function isSleep(node: ESTree.Node) {
      if (node.type === 'NewExpression') {
        return (
          node.callee.type === 'Identifier' &&
          node.callee.name === 'Promise' &&
          resolvesAfterTimeout(node)
        )
      }

      if (node.type !== 'CallExpression') return false

      return (
        timerBinding(context.sourceCode, node.callee) === 'setTimeout' ||
        isMember(node.callee, 'Bun', 'sleep')
      )
    }

    return {
      CallExpression(node) {
        if (
          isMember(node.callee, 'vi', 'useFakeTimers') ||
          isMember(node.callee, 'jest', 'useFakeTimers')
        ) {
          fakeTimers = true
        }

        if (isTimedWait(node)) timedWaits.push(node)
      },
      Property(node) {
        if (waitsUntilIdle(node)) timedWaits.push(node)
      },
      FunctionDeclaration(node) {
        if (node.id) recordHelper(node.id.name, node)
      },
      VariableDeclarator(node) {
        if (node.id.type === 'Identifier') recordHelper(node.id.name, node.init)
      },
      AwaitExpression(node) {
        if (!inTestBody(node, runNow)) return

        const { argument } = node

        if (isSleep(argument)) {
          sleeps.push(node)
        } else if (argument.type === 'CallExpression' && argument.callee.type === 'Identifier') {
          helperCalls.push([node, argument.callee.name])
        }
      },
      'Program:exit'(program) {
        for (const [node, name] of helperCalls) {
          const value = helpers.get(name)

          if (value && isSleep(value)) sleeps.push(node)
        }

        reportAllowed(
          context,
          program,
          [...(fakeTimers ? [] : sleeps), ...timedWaits],
          'sleep',
          undefined,
          (node) => (timedWaits.includes(node) ? 'timedWait' : 'sleep'),
        )
      },
    }
  },
})
