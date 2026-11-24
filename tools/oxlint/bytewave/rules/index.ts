import { definePlugin } from '@oxlint/plugins'

import { noComments } from './no-comments.ts'
import { noElapsedTimeBound } from './no-elapsed-time-bound.ts'
import { noFixedSleep } from './no-fixed-sleep.ts'
import { noFlakeMasking } from './no-flake-masking.ts'
import { noImportedMutation } from './no-imported-mutation.ts'
import { noSharedSignal } from './no-shared-signal.ts'
import { noSilentCatch } from './no-silent-catch.ts'
import { noUnsignaledPoll } from './no-unsignaled-poll.ts'
import { paddingBetweenBlocks } from './padding-between-blocks.ts'

const bytewavePlugin = definePlugin({
  meta: { name: 'bytewave' },
  rules: {
    'no-comments': noComments,
    'no-elapsed-time-bound': noElapsedTimeBound,
    'no-fixed-sleep': noFixedSleep,
    'no-flake-masking': noFlakeMasking,
    'no-imported-mutation': noImportedMutation,
    'no-shared-signal': noSharedSignal,
    'no-silent-catch': noSilentCatch,
    'no-unsignaled-poll': noUnsignaledPoll,
    'padding-between-blocks': paddingBetweenBlocks,
  },
})

export default bytewavePlugin
