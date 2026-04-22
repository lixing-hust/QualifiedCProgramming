# Contract reasoning: reverse_digits

## Source semantics

Raw task: input a non-negative integer `n` and return the integer obtained by reversing its decimal digits. The implementation initializes `ans = 0`, then repeatedly appends the current least significant decimal digit of `n` to `ans` with `ans = ans * 10 + n % 10`, and drops that digit with `n = n / 10`. For `n = 0`, the loop is skipped and the function returns `0`.

The target function is pure scalar computation. It has no pointer parameters, no heap memory, no global state, and no I/O.

## Mathematical specification

There is no existing common Coq definition in the CAV input set for decimal digit reversal. This task needs a small topic-specific Coq function, analogous to the existing `digit_sum_z` pattern.

The `.v` file defines:

- `reverse_digits_fuel n acc fuel`, a fuel-bounded model of the loop state.
- `reverse_digits_z n`, initialized with `acc = 0` and `fuel = Z.to_nat n`.

The fuel is sufficient for non-negative `n` because repeated quotient by 10 strictly decreases positive `n`; it also gives the intended base case `reverse_digits_z 0 = 0`.

The C postcondition states:

```c
__return == reverse_digits_z(n@pre)
```

## Preconditions and safety

The raw problem gives `n >= 0`. Since the C parameter has type `int`, the contract also states `n <= INT_MAX`.

The update `ans = ans * 10 + n % 10` may overflow even when the original input is a valid `int` (for example, reversing a large number). The contract therefore requires:

```c
reverse_digits_z(n) <= INT_MAX
```

The mathematical result is non-negative for non-negative input, so no lower result bound is needed beyond the semantic definition. Intermediate accumulated values are prefixes of the final reversed decimal representation, so the final-result bound is the intended contract-level overflow boundary; Verify may expose any additional local arithmetic obligations with invariants, but those are not added in Contract.

## Memory

The function uses only scalar locals. The heap assertion is `emp` in both precondition and postcondition.

## Coq dependency decision

`input/reverse_digits.v` is needed because the result relation is not expressible with a simple built-in arithmetic expression and no reusable public `reverse_digits` definition was found. The `.v` file contains only task-specific definitions and no proof obligations.
