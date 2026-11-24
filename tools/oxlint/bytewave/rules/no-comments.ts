import { defineRule } from '@oxlint/plugins'

import {
  allowlistProperties,
  allowanceFor,
  readStringArrayOption,
  readOptionObject,
  readBooleanOption,
} from '../lib/allowlist.ts'

import type { Comment, ESTree, Scope } from '@oxlint/plugins'

const coreDirectives = [
  /^(?:prettier|oxfmt)-ignore(?:-start|-end)?(?:\s|$)/u,
  /^(?:@|#)__(?:PURE|NO_SIDE_EFFECTS|INLINE|NOINLINE)__$/u,
  /^@vite-ignore$/u,
  /^@(?:vitest|jest)-environment\s+\S/u,
  /^\/\s*<(?:reference|amd-module|amd-dependency)\s/u,
  /^#\s*source(?:Mapping)?URL=/u,
  /^(?:SPDX-License-Identifier:|@license\b)/mu,
  /^(?:@jsx|@jsxFrag|@jsxImportSource|@jsxRuntime)\s+\S/u,
]

function normalizeComment(comment: Comment) {
  return comment.value
    .replace(/^!/u, '')
    .replaceAll(/^\s*\*\s?/gmu, '')
    .trim()
}

function isFunctionalDirective(comment: Comment, extraDirectives: readonly RegExp[]) {
  if (comment.type === 'Shebang') return true

  const value = normalizeComment(comment)

  return (
    coreDirectives.some((pattern) => pattern.test(value)) ||
    extraDirectives.some((pattern) => pattern.test(value))
  )
}

function hasAllowedPrefix(comment: Comment, prefixes: readonly string[]) {
  const value = comment.value.trimStart()

  return (
    comment.type === 'Line' &&
    comment.loc.start.line === comment.loc.end.line &&
    prefixes.some(
      (prefix) => value.startsWith(`${prefix}:`) && value.slice(prefix.length + 1).trim() !== '',
    )
  )
}

export const noComments = defineRule({
  meta: {
    type: 'suggestion',
    schema: [
      {
        type: 'object',
        properties: {
          ...allowlistProperties,
          allowPrefixes: { type: 'array', items: { type: 'string', minLength: 1 } },
          allowDirectives: { type: 'array', items: { type: 'string', minLength: 1 } },
          allowPublicApiDoc: { type: 'boolean' },
          publicApi: { type: 'array', items: { type: 'string', minLength: 1 } },
        },
        additionalProperties: false,
      },
    ],
    docs: {
      description:
        'Disallow prose and suppression comments; allow only functional build/format directives, WARNING: footgun notes, and optional exported public API TSDoc.',
    },
    messages: {
      forbidden:
        'Remove this comment; express intent through clear naming and types. Only functional directives, single-line WARNING: notes for genuine footguns, and configured public API TSDoc are allowed.',
      stale:
        'This file now has {{count}} disallowed comments; lower its bytewave/no-comments allowlist entry for {{path}} in oxlint.config.ts to {{count}}, or remove the entry at 0.',
    },
  },
  create(context) {
    const source = context.sourceCode
    const options = readOptionObject(context)
    const filename = context.physicalFilename.replaceAll('\\', '/')
    const prefixes = readStringArrayOption(options, 'allowPrefixes') ?? ['WARNING']
    const extraDirectives = (readStringArrayOption(options, 'allowDirectives') ?? []).map(
      (pattern) => new RegExp(pattern, 'u'),
    )
    const publicApiPatterns = readStringArrayOption(options, 'publicApi')
    const allowPublicApiDoc = readBooleanOption(options, 'allowPublicApiDoc') ?? false
    const publicFile =
      publicApiPatterns !== undefined
        ? publicApiPatterns.some((pattern) => new RegExp(pattern, 'u').test(filename))
        : allowPublicApiDoc

    const documented = new Set<number>()
    const declarations = new Set<ESTree.Node>()
    const members: ESTree.Node[] = []
    const references: (
      | ESTree.TSTypeReference
      | ESTree.TSInterfaceHeritage
      | ESTree.TSClassImplements
    )[] = []

    function document(node: ESTree.Node) {
      const comments = source.getCommentsBefore(node)
      let [start] = node.range

      while (comments.length > 0) {
        const last = comments.at(-1)

        if (!last || !isFunctionalDirective(last, extraDirectives)) break

        if (source.text.slice(last.range[1], start).trim() !== '') return

        ;[start] = last.range
        comments.pop()
      }

      const comment = comments.at(-1)

      if (
        comment?.type === 'Block' &&
        comment.value.startsWith('*') &&
        !/@(?:internal|private)\b/u.test(comment.value) &&
        source.text.slice(comment.range[1], start).trim() === ''
      ) {
        documented.add(comment.range[0])
      }
    }

    function collectMember(node: ESTree.Node) {
      members.push(node)
    }

    function isExposed(node: ESTree.Node) {
      let ancestor = node

      while (!declarations.has(ancestor)) {
        if (
          ancestor.type === 'Program' ||
          ancestor.type === 'BlockStatement' ||
          ancestor.type === 'StaticBlock' ||
          ('accessibility' in ancestor &&
            (ancestor.accessibility === 'private' || ancestor.accessibility === 'protected')) ||
          ('key' in ancestor && ancestor.key.type === 'PrivateIdentifier') ||
          (ancestor.parent.type === 'ArrowFunctionExpression' && ancestor.parent.body === ancestor)
        ) {
          return false
        }

        ancestor = ancestor.parent
      }

      return true
    }

    return {
      Property: collectMember,
      TSInterfaceDeclaration: collectMember,
      TSTypeAliasDeclaration: collectMember,
      TSPropertySignature: collectMember,
      TSMethodSignature: collectMember,
      TSCallSignatureDeclaration: collectMember,
      TSConstructSignatureDeclaration: collectMember,
      TSIndexSignature: collectMember,
      TSEnumMember: collectMember,
      MethodDefinition: collectMember,
      PropertyDefinition: collectMember,
      TSTypeReference(node) {
        references.push(node)
      },
      TSInterfaceHeritage(node) {
        references.push(node)
      },
      TSClassImplements(node) {
        references.push(node)
      },
      'Program:exit'(program) {
        if (publicFile) {
          const exportedNames = new Set<string>()
          const ambientFile =
            /\.d\.[cm]?ts$/u.test(context.physicalFilename) &&
            program.body.every(
              (node) => node.type !== 'ImportDeclaration' && !node.type.startsWith('Export'),
            )

          for (const node of program.body) {
            if (ambientFile || (node.type === 'TSModuleDeclaration' && node.declare)) {
              declarations.add(node)
            }

            if (node.type === 'ExportNamedDeclaration') {
              document(node)

              if (node.declaration) {
                declarations.add(node.declaration)
              } else if (node.source === null) {
                for (const specifier of node.specifiers) {
                  if (specifier.local.type === 'Identifier') {
                    exportedNames.add(specifier.local.name)
                  }
                }
              }
            } else if (node.type === 'ExportDefaultDeclaration') {
              document(node)

              if (node.declaration.type === 'Identifier') {
                exportedNames.add(node.declaration.name)
              } else {
                declarations.add(node.declaration)
              }
            } else if (node.type === 'ExportAllDeclaration') {
              document(node)
            }
          }

          for (const node of program.body) {
            if (
              source.getDeclaredVariables(node).some((variable) => exportedNames.has(variable.name))
            ) {
              declarations.add(node)
            }
          }

          let previousSize = -1

          while (previousSize !== declarations.size) {
            previousSize = declarations.size

            for (const reference of references) {
              const name =
                reference.type === 'TSTypeReference' ? reference.typeName : reference.expression

              if (name.type !== 'Identifier' || !isExposed(reference)) continue

              let scope: Scope | null = source.getScope(reference)

              while (scope) {
                const variable = scope.set.get(name.name)

                if (variable) {
                  for (const definition of variable.defs) {
                    if (
                      definition.node.type === 'TSInterfaceDeclaration' ||
                      definition.node.type === 'TSTypeAliasDeclaration'
                    ) {
                      declarations.add(definition.node)
                    }
                  }

                  break
                }

                scope = scope.upper
              }
            }
          }

          for (const node of declarations) document(node)

          for (const node of members) {
            if (isExposed(node)) document(node)
          }
        }

        const violations = source
          .getAllComments()
          .filter(
            (comment) =>
              !isFunctionalDirective(comment, extraDirectives) &&
              !hasAllowedPrefix(comment, prefixes) &&
              !documented.has(comment.range[0]),
          )

        const [path, count] = allowanceFor(context) ?? ['', 0]

        if (violations.length < count) {
          context.report({
            node: program,
            messageId: 'stale',
            data: { path, count: String(violations.length) },
          })

          return
        }

        if (violations.length === count) return

        for (const comment of violations) {
          context.report({ loc: comment.loc, messageId: 'forbidden' })
        }
      },
    }
  },
})
