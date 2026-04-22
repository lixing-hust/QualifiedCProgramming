# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next right-hand index to inspect for the adjacent pair `(i - 1, i)`. At the loop head, all adjacent pair indices `j` with `1 <= j < i` have already been checked.
- Required postcondition: a return value of `1` needs an existential adjacent equal pair; a return value of `0` needs a universal fact that every valid adjacent pair is unequal, while preserving `IntArray::full(a, n, l)`.
- Stable facts that should stay in the invariant: `a == a@pre`, `n == n@pre`, ownership `IntArray::full(a, n, l)`, a range fact for `i`, and the processed-prefix property `(forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1])`.
- Initialization check: after the `for` initializer, `i == 1`, so the processed-prefix property is vacuous. The bound must support edge cases `n == 0` and `n == 1`, where the loop body is never entered and `i` remains `1`; therefore `i <= n + 1` is safer than `i <= n`.
- Preservation expectation: if `a[i] == a[i - 1]`, the function returns immediately and can use current `i` as the existential witness. Otherwise the newly checked pair is unequal, extending the processed-prefix property from `< i` to `< i + 1`.
- Exit usefulness: when the loop exits, `!(i < n)` plus `i <= n + 1` and the processed-prefix fact should imply the final universal postcondition. A loop-exit `Assert` will restate the exact full-range universal fact before `return 0`.

## Planned edit

- Add a loop invariant with bounds, unchanged parameter facts, array ownership, and the checked-prefix adjacent-inequality property.
- Add one loop-exit assertion fixing the universal no-adjacent-equal property over `1 <= j < n` before the final return.

## Round 2

- Observed failure after Round 1: `logs/qcp_run.log` reports `Fail to Remove Memory Permission of i` at the final `return 0` line, immediately after the loop-exit `Assert`.
- Diagnosis: this matches the known assertion-placement issue from `doc/experiences/ASSERTION.md`: a loop-exit assertion after a `for` loop can interfere with cleanup of the local loop variable permission.
- Planned repair: delete the final loop-exit `Assert` and keep the invariant as the only semantic summary. The invariant says `(forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1])`; on loop exit, the generated return witness should have access to the negated loop guard `i >= n`, which is enough to derive the postcondition universal over `j < n`.
- After this edit, clear generated files and rerun `symexec` so no partial VCs from the failed run are reused.
