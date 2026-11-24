import path from 'node:path'

export type OxlintRuleSeverity = 'off' | 'warn' | 'error'

export type OxlintRuleEntry =
  | OxlintRuleSeverity
  | readonly [OxlintRuleSeverity, ...(readonly object[])]

export type OxlintRules = Record<string, OxlintRuleEntry>
export type OxlintJsPlugin = string | { readonly name: string; readonly specifier: string }

export interface OxlintOverride {
  readonly files: readonly string[]
  readonly rules?: OxlintRules
  readonly plugins?: readonly string[]
}

export interface BytewaveNoCommentsOptions {
  readonly allow?: Record<string, number>
  readonly allowPrefixes?: readonly string[]
  readonly allowDirectives?: readonly string[]
  readonly allowPublicApiDoc?: boolean
  readonly publicApi?: readonly string[]
}

export interface BytewaveOxlintOptions {
  readonly vue?: boolean
  readonly testing?: boolean
  readonly vitest?: boolean
  readonly tailwind?: boolean
  readonly ignorePatterns?: readonly string[]
  readonly plugins?: readonly string[]
  readonly jsPlugins?: readonly OxlintJsPlugin[]
  readonly rules?: OxlintRules
  readonly overrides?: readonly OxlintOverride[]
  readonly settings?: Record<string, object>
  readonly noComments?: BytewaveNoCommentsOptions
}

export interface BytewaveOxlintConfig {
  readonly options: { readonly reportUnusedDisableDirectives: 'error' }
  readonly ignorePatterns: readonly string[]
  readonly plugins: readonly string[]
  readonly jsPlugins: readonly OxlintJsPlugin[]
  readonly rules: OxlintRules
  readonly overrides?: readonly OxlintOverride[]
  readonly settings?: Record<string, object>
}

export const defaultIgnorePatterns = [
  '.nuxt/**',
  '.output/**',
  '.alchemy/**',
  'coverage/**',
  'dist/**',
  'node_modules/**',
  'test-results/**',
  'generated/**',
  '.agent/**',
  '.agents/**',
  '.claude/**',
  '.codex/**',
  '.continue/**',
  '.cursor/**',
  '.gemini/**',
  '.opencode/**',
  '.pi/**',
  '.roo/**',
  '.windsurf/**',
  'tools/oxlint/bytewave/**',
] as const

export const vueEventListenerRestrictions = [
  {
    object: 'window',
    property: 'addEventListener',
    message: 'Use VueUse useEventListener instead — it cleans up on unmount.',
  },
  {
    object: 'window',
    property: 'removeEventListener',
    message: 'Use VueUse useEventListener instead — manual removal is unnecessary.',
  },
  {
    object: 'document',
    property: 'addEventListener',
    message: 'Use VueUse useEventListener instead — it cleans up on unmount.',
  },
  {
    object: 'document',
    property: 'removeEventListener',
    message: 'Use VueUse useEventListener instead — manual removal is unnecessary.',
  },
] as const

export function defineBytewaveOxlintConfig(
  options: BytewaveOxlintOptions = {},
): BytewaveOxlintConfig {
  const plugins = new Set<string>(['typescript', 'unicorn', 'oxc', ...(options.plugins ?? [])])

  if (options.vue) plugins.add('vue')

  if (options.vitest) plugins.add('vitest')

  const noCommentsRule: OxlintRuleEntry = options.noComments
    ? ['error', options.noComments]
    : 'error'

  const baseRules: OxlintRules = {
    'no-unused-vars': [
      'warn',
      {
        varsIgnorePattern: '^_',
        argsIgnorePattern: '^_',
      },
    ],
    'typescript/no-explicit-any': 'error',
    'oxc/no-accumulating-spread': 'error',
    'anti-slop/no-chained-type-assertions': 'error',
    'anti-slop/no-conditional-empty-object-spread': 'error',
    'anti-slop/no-known-value-widening': 'error',
    'anti-slop/no-module-mocking': 'error',
    'anti-slop/no-object-parameters': 'error',
    'anti-slop/no-reduce-accumulator-copy': 'error',
    'anti-slop/no-reflect-apply': 'error',
    'anti-slop/no-reflect-get': 'error',
    'anti-slop/no-runtime-typeof': ['error', { allowInTypeGuards: true }],
    'anti-slop/no-shape-in-symbol-names': 'error',
    'anti-slop/no-unknown-parameters': 'error',
    'anti-slop/no-unknown-returns': 'error',
    'anti-slop/no-unknown-type-aliases': 'error',
    'anti-slop/no-unsafe-dictionary-type': 'error',
    'anti-slop/no-widen-then-assert': 'error',
    'bytewave/no-comments': noCommentsRule,
    'bytewave/no-silent-catch': 'error',
    'bytewave/padding-between-blocks': 'error',
    ...(options.vue
      ? { 'no-restricted-properties': ['error', ...vueEventListenerRestrictions] }
      : {}),
    ...(options.testing
      ? {
          'bytewave/no-elapsed-time-bound': 'error',
          'bytewave/no-fixed-sleep': 'error',
          'bytewave/no-flake-masking': 'error',
          'bytewave/no-imported-mutation': 'error',
          'bytewave/no-shared-signal': 'error',
          'bytewave/no-unsignaled-poll': 'error',
        }
      : {}),
    ...(options.vitest ? { 'vitest/no-commented-out-tests': 'error' } : {}),
    ...options.rules,
  }

  const jsPlugins: OxlintJsPlugin[] = [
    ...(options.tailwind ? ['oxlint-tailwindcss'] : []),
    {
      name: 'anti-slop',
      specifier: path.join(import.meta.dirname, 'anti-slop/index.ts'),
    },
    {
      name: 'bytewave',
      specifier: path.join(import.meta.dirname, 'rules/index.ts'),
    },
    ...(options.jsPlugins ?? []),
  ]

  return {
    options: { reportUnusedDisableDirectives: 'error' },
    ignorePatterns: [...new Set([...defaultIgnorePatterns, ...(options.ignorePatterns ?? [])])],
    plugins: [...plugins],
    jsPlugins,
    rules: baseRules,
    ...(options.overrides && options.overrides.length > 0
      ? { overrides: [...options.overrides] }
      : {}),
    ...(options.settings ? { settings: options.settings } : {}),
  }
}

export interface BytewavePromisesOptions {
  readonly ignorePatterns?: readonly string[]
  readonly overrides?: readonly OxlintOverride[]
}

export function defineBytewavePromisesConfig(options: BytewavePromisesOptions = {}) {
  return {
    ignorePatterns: [...new Set([...defaultIgnorePatterns, ...(options.ignorePatterns ?? [])])],
    plugins: ['typescript'],
    categories: { correctness: 'off' },
    options: { typeAware: true },
    rules: {
      'typescript/no-floating-promises': [
        'error',
        {
          ignoreVoid: true,
          allowForKnownSafeCalls: [{ from: 'package', name: ['test', 'it'], package: 'node:test' }],
        },
      ],
    },
    ...(options.overrides && options.overrides.length > 0
      ? { overrides: [...options.overrides] }
      : {}),
  }
}
