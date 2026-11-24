import { defineBytewaveOxlintConfig } from './tools/oxlint/bytewave/presets.ts'

export default defineBytewaveOxlintConfig({
  testing: true,
  ignorePatterns: ['.lake/**', 'test/fixtures/**'],
  overrides: [
    {
      files: ['src/**/*.ts', 'scripts/**/*.mjs', 'test/**/*.ts'],
      rules: {
        'anti-slop/no-shape-in-symbol-names': 'off',
        'anti-slop/no-runtime-typeof': 'off',
        'anti-slop/no-conditional-empty-object-spread': 'off',
        'anti-slop/no-unknown-parameters': 'off',
        'anti-slop/no-unknown-returns': 'off',
        'anti-slop/no-known-value-widening': 'off',
        'anti-slop/no-chained-type-assertions': 'off',
        'anti-slop/no-unsafe-dictionary-type': 'off',
        'anti-slop/no-object-parameters': 'off',
      },
    },
    {
      files: ['src/translate.ts', 'src/runner.ts'],
      rules: {
        'typescript/no-explicit-any': 'off',
      },
    },
  ],
})
