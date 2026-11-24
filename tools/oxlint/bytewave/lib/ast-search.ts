import type { ESTree } from '@oxlint/plugins'

function isNode(value: unknown): value is ESTree.Node {
  return (
    typeof value === 'object' && value !== null && 'type' in value && typeof value.type === 'string'
  )
}

export function containsNode(root: ESTree.Node, predicate: (node: ESTree.Node) => boolean) {
  const pending: ESTree.Node[] = [root]

  while (pending.length > 0) {
    const node = pending.pop()

    if (!node) break

    if (predicate(node)) return true

    for (const [key, value] of Object.entries(node)) {
      if (key === 'parent') continue

      if (Array.isArray(value)) {
        for (const item of value) {
          if (isNode(item)) pending.push(item)
        }
      } else if (isNode(value)) {
        pending.push(value)
      }
    }
  }

  return false
}
