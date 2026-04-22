# Contract reasoning for digit_sum

## Source semantics

The raw task defines `digit_sum(int n)` for nonnegative integers. The implementation initializes `sum` to `0`, then repeatedly adds the low decimal digit `n % 10` and shrinks `n` with integer division by `10` until `n == 0`. The required boundary behavior is `digit_sum(0) = 0`, which the loop satisfies because the body is skipped.

The C function has no pointer arguments, no heap ownership, and no side effects outside local scalar variables.

## Input domain and arithmetic safety

The formal precondition restricts `n` to `0 <= n && n <= INT_MAX`. This matches the natural-language nonnegative-input requirement and keeps the input inside the usual C `int` domain explicitly.

For every loop iteration under `n > 0`, division and remainder by the positive constant `10` are defined. The added digit is in the range `0..9` for nonnegative `n`. For `int` inputs, the decimal digit sum is small enough to stay inside `int`, so no extra final-result overflow bound is needed.

## Mathematical specification

No reusable public Coq definition for integer digit sum was found in the local CAV inputs or common libraries. The contract therefore uses a task-local Coq definition:

- `digit_sum_z : Z -> Z`

The definition is fuelled by `Z.to_nat n`. For `n <= 0` it returns `0`; for positive `n` it returns `Z.rem n 10 + digit_sum_fuel (Z.quot n 10) k`. This mirrors the C implementation's nonnegative `% 10` and `/ 10` steps, including the `n = 0` base case.

## Contract shape

The C postcondition states exactly that `__return == digit_sum_z(n@pre)`. The contract does not include loop invariants, assertions, bridge assertions, or loop-exit assertions, because those belong to the Verify phase.

## Coq dependency decision

`input/digit_sum.v` is needed because the task-specific decimal digit-sum function is not available as a public reusable Coq name. The `.v` file contains only this problem-specific mathematical definition.
