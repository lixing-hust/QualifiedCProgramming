# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next index to compare, so at the loop head the processed region is exactly the prefix `[0, i)`.
- Required postcondition:
  - if the function returns `0`, there must exist a first mismatching position inside the shared-length lists
  - if the function returns `1`, the full lists must be pointwise equal so that `array_equal_spec(la, lb) = 1`
- Stable facts to preserve across iterations:
  - bounds `0 <= i <= n`
  - unchanged parameters `n == n@pre`, `a == a@pre`, `b == b@pre`
  - both array ownership facts `IntArray::full(a, n, la)` and `IntArray::full(b, n, lb)`
  - semantic prefix fact `(forall (j: Z), (0 <= j && j < i) => la[j] == lb[j])`
- Initialization check:
  - before the first loop test, `i == 0`
  - the quantified prefix-equality fact is vacuous
- Preservation expectation:
  - on the mismatch branch, the function returns immediately, so the invariant only needs to describe the loop-head state before the read
  - on the equal branch, the current comparison plus the old prefix fact should extend equality from `[0, i)` to `[0, i + 1)`
- Exit usefulness:
  - when the loop stops, `i == n`
  - the prefix-equality fact becomes equality over the whole valid index range of both length-`n` arrays, which is the exact semantic bridge needed for `return 1`

## Planned edit

- Add one loop invariant carrying the processed-prefix equality fact and unchanged array resources.
- Add one loop-exit assertion fixing `i == n` and restating full-range equality before `return 1`.

## Round 2

- First rerun blocker: the parser rejected `With la, lb` with `unexpected PT_COMMA, expecting PT_REQUIRE`.
- Diagnosis:
  - the active annotated copy still matched the formal contract semantically
  - the issue was frontend syntax compatibility, not a need to redesign `Require` or `Ensure`
- Change:
  - normalize only the active annotated copy to `With la lb`
- Expectation:
  - this should let `symexec` reach the function body so the real annotation quality can be tested

## Round 3

- Second rerun blocker: `symexec` reported `Expected loop after loop invariant`.
- Diagnosis:
  - this frontend requires `Inv` immediately before the `for` statement
  - placing `Inv` as the first statement inside the loop body does not attach it to the loop head
- Change:
  - move the invariant block to the line directly above `for (i = 0; i < n; ++i)`
- Result:
  - after this control-point fix, `symexec` completed successfully and generated fresh Coq files
