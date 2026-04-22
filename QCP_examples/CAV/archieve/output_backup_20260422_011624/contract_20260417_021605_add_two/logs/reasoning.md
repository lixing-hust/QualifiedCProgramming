## Function

`add_two(int a, int b)` is a pure scalar function that returns the sum of its two integer inputs.

## Semantics

- Original semantics: `return a + b;`
- No interface rewrite is needed.
- No heap, pointer, array, or external resource is involved.

## Boundary Analysis

- The problem statement guarantees `a` and `b` are 32-bit signed integers.
- The problem statement also guarantees the result is within the 32-bit signed integer range.
- For contract writing, the key safety condition is that `a + b` must stay within `int` range.
- A direct precondition `INT_MIN <= a + b && a + b <= INT_MAX` is the smallest condition aligned with the stated guarantee.

## Memory Analysis

- The function does not read or write extra memory.
- The resource footprint is `emp` in both precondition and postcondition.

## Coq Dependency Decision

- No extra mathematical abstraction is needed.
- The postcondition can express the full semantics directly as `__return == a + b`.
- Therefore `input/add_two.v` is unnecessary.

## Contract Shape

- `Require`: bounded sum and `emp`
- `Ensure`: returned value equals the mathematical sum of the pre-state inputs, and `emp`

## Verify-Phase Exclusions

- No loop invariants are needed because there is no loop.
- No intermediate assertions, bridge assertions, or proof-oriented annotations should appear in the contract file.
