# Annotation Reasoning

## Iteration 1: parse blocker before any loop reasoning

- Observation: the first `symexec` run failed before symbolic execution with `Unrecognized character: '''` at the annotated postcondition line containing `repeat_Z('a', n)`.
- Diagnosis: this frontend is parser-fragile around char literals in the active annotated copy. The nearby verify examples already use numeric literals like `0` in annotated string code for the same reason.
- Planned change: keep the input contract untouched, but make the active annotated postcondition parser-safe by replacing `'a'` with `97`.
- Why this may help: it removes the frontend blocker so the verifier can actually inspect the loop and generate real VCs.

## Iteration 2: expected loop invariant shape

- Observation: `string_set_a` is a forward fill over an initially undefined `char` buffer, followed by a single terminator write at `s[n]`.
- Required post-state at loop exit: the first `n` cells must contain `97`, and the final cell `s[n]` is still unwritten until after the loop.
- Invariant design:
  - `0 <= i <= n`
  - the written prefix is `CharArray::full(s, i, repeat_Z(97, i))`
  - the remaining suffix is `CharArray::undef_seg(s, i, n + 1)`
- Initialization check: at `i = 0`, `repeat_Z(97, 0)` is the empty prefix and the whole buffer remains undefined, matching the precondition.
- Preservation check: one loop iteration writes exactly `s[i] = 97`, so the prefix extends by one cell and the undefined suffix shrinks from `[i, n + 1)` to `[i + 1, n + 1)`.
- Exit usefulness: when the loop stops, `i == n`, so the invariant yields `CharArray::full(s, n, repeat_Z(97, n)) * CharArray::undef_seg(s, n, n + 1)`. The final statement `s[n] = 0` should then close to the required full array content.
- Planned change: attach this invariant immediately before the `for` loop in the active annotated copy.
