# Contract reasoning: fibonacci_mod

## Source semantics

The raw function computes the Fibonacci sequence with a rolling pair:

- `a` stores the previous Fibonacci value modulo `mod`.
- `b` stores the current Fibonacci value modulo `mod`.
- for each `i` from `2` through `n`, `c = (a + b) % mod`, then the pair shifts to `(b, c)`.

The boundary cases are:

- `n == 0`: return `0`.
- `n == 1`: skip the loop and return `1 % mod`.
- `n >= 2`: return the stepwise modulo recurrence at index `n`.

The input assumptions from the problem are `n >= 0` and `mod > 0`.

## Contract choices

The postcondition refers to a task-specific Coq function `fib_mod_z(n, mod)` that mirrors the stepwise modulo recurrence. This is clearer than specifying plain Fibonacci and then requiring downstream proofs to bridge it to modulo arithmetic.

The contract additionally constrains:

- `n < 2147483647`, so the loop increment remains within signed `int`.
- `mod <= 1073741824`, so if `0 <= a < mod` and `0 <= b < mod`, then `a + b <= 2147483646`; this makes the addition before `% mod` signed-int safe.

The result is specified exactly as:

```text
__return == fib_mod_z(n@pre, mod@pre)
```

The Coq definition uses `Z.rem`, matching the C `%` operator used by existing repository examples. Under `mod > 0` and nonnegative operands, this is the expected nonnegative modulo result.

## Memory and interface

The function is pure scalar computation:

- no pointer arguments
- no heap ownership
- no global state
- no allocation

Therefore the heap part of both precondition and postcondition is `emp`.

The original C interface is already verification-friendly and is preserved unchanged.

## Coq dependency decision

`input/fibonacci_mod.v` is needed because the stepwise modulo recurrence is specific to this task. The file contains only the logic function required by the C contract and no proof-stage invariant or assertion material.
