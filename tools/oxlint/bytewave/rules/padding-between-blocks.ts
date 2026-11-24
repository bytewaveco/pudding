import { defineRule } from '@oxlint/plugins'

import type { Comment, ESTree } from '@oxlint/plugins'

type Statement = ESTree.Program['body'][number]

function unwrapExport(node: Statement) {
  return node.type === 'ExportNamedDeclaration' || node.type === 'ExportDefaultDeclaration'
    ? node.declaration
    : node
}

function isImport(node: Statement) {
  return node.type === 'ImportDeclaration' || node.type === 'TSImportEqualsDeclaration'
}

function isOverloadPair(previous: Statement, next: Statement) {
  const prevDecl = unwrapExport(previous)
  const nextDecl = unwrapExport(next)

  return (
    prevDecl?.type === 'TSDeclareFunction' &&
    (nextDecl?.type === 'TSDeclareFunction' || nextDecl?.type === 'FunctionDeclaration') &&
    prevDecl.id?.name === nextDecl.id?.name
  )
}

function isMultiline(node: ESTree.Node) {
  return node.loc.end.line > node.loc.start.line
}

function isFunctionOrClassInit(node: ESTree.Node | null | undefined) {
  return (
    node?.type === 'ArrowFunctionExpression' ||
    node?.type === 'FunctionExpression' ||
    node?.type === 'ClassExpression'
  )
}

function isPaddedBlock(node: Statement) {
  const unwrapped = unwrapExport(node)

  if (!unwrapped) return false

  if (unwrapped.type === 'FunctionDeclaration' || unwrapped.type === 'ClassDeclaration') {
    return true
  }

  if (!isMultiline(node)) return false

  if (
    unwrapped.type === 'IfStatement' ||
    unwrapped.type === 'ForStatement' ||
    unwrapped.type === 'ForInStatement' ||
    unwrapped.type === 'ForOfStatement' ||
    unwrapped.type === 'WhileStatement' ||
    unwrapped.type === 'DoWhileStatement' ||
    unwrapped.type === 'SwitchStatement' ||
    unwrapped.type === 'TryStatement' ||
    unwrapped.type === 'TSInterfaceDeclaration' ||
    unwrapped.type === 'TSEnumDeclaration' ||
    unwrapped.type === 'TSModuleDeclaration' ||
    unwrapped.type === 'TSTypeAliasDeclaration'
  ) {
    return true
  }

  if (unwrapped.type === 'VariableDeclaration') {
    return unwrapped.declarations.some((declarator) => isFunctionOrClassInit(declarator.init))
  }

  return false
}

function needsBlankLine(previous: Statement, next: Statement) {
  if (isImport(previous) && isImport(next)) return false

  if (isImport(previous) !== isImport(next)) return true

  if (isOverloadPair(previous, next)) return false

  if (previous.loc.end.line === next.loc.start.line) return false

  return isPaddedBlock(previous) || isPaddedBlock(next)
}

export const paddingBetweenBlocks = defineRule({
  meta: {
    type: 'layout',
    schema: [],
    fixable: 'whitespace',
    docs: {
      description:
        'Require blank lines around structural blocks, functions, classes, and multi-line type/function declarations while keeping compact single-line statements together.',
    },
    messages: {
      padding: 'Add a blank line to separate this block from the adjacent statement.',
    },
  },
  create(context) {
    const source = context.sourceCode.text

    function check(statements: readonly Statement[]) {
      for (const [index, next] of statements.entries()) {
        const previous = statements[index - 1]

        if (previous === undefined || !needsBlankLine(previous, next)) continue

        let before: Statement | Comment = previous
        let after: Statement | Comment = next

        for (const comment of context.sourceCode.getCommentsBefore(next)) {
          if (comment.range[0] < previous.range[1]) continue

          if (comment.loc.start.line === before.loc.end.line) {
            before = comment
          } else {
            after = comment

            break
          }
        }

        const gap = source.slice(before.range[1], after.range[0])

        if (after.loc.start.line > before.loc.end.line + 1 || /\S/u.test(gap)) continue

        context.report({
          node: next,
          messageId: 'padding',
          fix(fixer) {
            const lineStart = source.lastIndexOf('\n', after.range[0] - 1) + 1
            const indentation = /^[\t ]*/u.exec(source.slice(lineStart, after.range[0]))?.[0] ?? ''
            const newline = gap.includes('\r\n') ? '\r\n' : '\n'

            return fixer.replaceTextRange(
              [before.range[1], after.range[0]],
              `${newline}${newline}${indentation}`,
            )
          },
        })
      }
    }

    return {
      Program: (node) => check(node.body),
      BlockStatement: (node) => check(node.body),
      StaticBlock: (node) => check(node.body),
      SwitchCase: (node) => check(node.consequent),
      TSModuleBlock: (node) => check(node.body),
    }
  },
})
