import type { Context, ESTree } from '@oxlint/plugins'

export const allowlistProperties = {
  allow: {
    type: 'object' as const,
    additionalProperties: { type: 'integer' as const, minimum: 1 },
  },
}

export const allowlistSchema = [
  {
    type: 'object' as const,
    properties: allowlistProperties,
    additionalProperties: false,
  },
]

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value)
}

export function readOptionObject(context: Context): Record<string, unknown> {
  const first = context.options[0]

  return isRecord(first) ? first : {}
}

export function readStringArrayOption(
  options: Record<string, unknown>,
  key: string,
): readonly string[] | undefined {
  const value = options[key]

  if (!Array.isArray(value)) return undefined

  return value.filter((item): item is string => typeof item === 'string' && item.length > 0)
}

export function readBooleanOption(
  options: Record<string, unknown>,
  key: string,
): boolean | undefined {
  const value = options[key]

  return typeof value === 'boolean' ? value : undefined
}

function readAllowMap(options: Record<string, unknown>): Record<string, number> {
  const raw = options.allow

  if (!isRecord(raw)) return {}

  const entries: [string, number][] = []

  for (const [key, value] of Object.entries(raw)) {
    if (typeof value === 'number' && Number.isInteger(value) && value >= 1) {
      entries.push([key, value])
    }
  }

  return Object.fromEntries(entries)
}

export function allowanceFor(context: Context): readonly [string, number] | undefined {
  const filename = context.physicalFilename.replaceAll('\\', '/')
  const allow = readAllowMap(readOptionObject(context))

  return Object.entries(allow).find(([path]) => filename === path || filename.endsWith(`/${path}`))
}

export function reportAllowed(
  context: Context,
  program: ESTree.Program,
  violations: readonly ESTree.Node[],
  messageId: string,
  data?: (node: ESTree.Node) => Record<string, string> | undefined,
  messageForNode?: (node: ESTree.Node) => string,
) {
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

  for (const node of violations) {
    context.report({
      node,
      messageId: messageForNode?.(node) ?? messageId,
      data: data?.(node),
    })
  }
}
