# Contract Issues: gcd_iterative

## Resolved

- The raw statement excludes `a == 0 && b == 0`; the generated precondition now preserves this exclusion as `0 < a + b` under `0 <= a && 0 <= b`.
- No pointer memory contract is needed because the function is scalar-only.
- A task-local Coq bridge was created because no existing local gcd wrapper was available.
- Verify later found that the original top-level disjunctive encoding `(a != 0 || b != 0)` combined with `a@pre` / `b@pre` in `Ensure` caused `symexec` to fail before VC generation with `Old value at pre is not determined`.
- Local probes showed that `a@pre` / `b@pre` themselves work, and the same program verifies through `symexec` when the nonzero condition is encoded without top-level disjunction.
- The contract was corrected by replacing `(a != 0 || b != 0)` with the equivalent non-disjunctive condition `0 < a + b`, relying on the existing nonnegative preconditions.

## Open

- None.
