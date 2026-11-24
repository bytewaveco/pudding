import { defineRule } from '@oxlint/plugins'

import { allowlistSchema, reportAllowed } from '../lib/allowlist.ts'

import type { ESTree, Scope } from '@oxlint/plugins'

const mutators = new Map<string, ReadonlySet<string>>([
  ['Object', new Set(['assign', 'defineProperty', 'defineProperties'])],
  ['Reflect', new Set(['set', 'defineProperty', 'deleteProperty'])],
])

function root(node: ESTree.Node) {
  let current = node

  while (current.type === 'MemberExpression') {
    current = current.object
  }

  return current.type === 'Identifier' ? current : undefined
}

function imported(scope: Scope | null, name: string) {
  for (let current = scope; current; current = current.upper) {
    const variable = current.set.get(name)

    if (variable) {
      return variable.defs.some(
        (definition) =>
          definition.type === 'ImportBinding' ||
          definition.node.type === 'ImportSpecifier' ||
          definition.node.type === 'ImportDefaultSpecifier' ||
          definition.node.type === 'ImportNamespaceSpecifier',
      )
    }
  }

  return false
}

function mutatedArgument(node: ESTree.CallExpression) {
  const { callee } = node

  if (
    callee.type !== 'MemberExpression' ||
    callee.computed ||
    callee.object.type !== 'Identifier' ||
    callee.property.type !== 'Identifier'
  ) {
    return null
  }

  if (!mutators.get(callee.object.name)?.has(callee.property.name)) {
    return null
  }

  const [target] = node.arguments

  return target && target.type !== 'SpreadElement' ? target : null
}

export const noImportedMutation = defineRule({
  meta: {
    type: 'problem',
    schema: allowlistSchema,
    docs: {
      description:
        'Inject test values through options or bindings instead of mutating properties of an imported module binding.',
    },
    messages: {
      mutation:
        'Mutating a property of an imported binding leaks shared module state across tests in the same isolate. Pass test values through function options, dependency injection, or a scoped override.',
      stale:
        'This file now has {{count}} imported-binding mutations; lower its bytewave/no-imported-mutation allowlist entry for {{path}} in oxlint.config.ts to {{count}}, or remove the entry at 0.',
    },
  },
  create(context) {
    if (!/\.(?:test|spec|fixture|test-utils)\.[cm]?[jt]sx?$/u.test(context.filename)) {
      return {}
    }

    const violations: ESTree.Node[] = []

    function record(node: ESTree.Node, expression: ESTree.Node) {
      const target = root(expression)

      if (target && imported(context.sourceCode.getScope(target), target.name)) {
        violations.push(node)
      }
    }

    return {
      AssignmentExpression(node) {
        if (node.left.type === 'MemberExpression') {
          record(node, node.left)
        }
      },
      CallExpression(node) {
        const target = mutatedArgument(node)

        if (target) record(node, target)
      },
      UnaryExpression(node) {
        if (node.operator === 'delete' && node.argument.type === 'MemberExpression') {
          record(node, node.argument)
        }
      },
      'Program:exit'(program) {
        reportAllowed(context, program, violations, 'mutation')
      },
    }
  },
})
