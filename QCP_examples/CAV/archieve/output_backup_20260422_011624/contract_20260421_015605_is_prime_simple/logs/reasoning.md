# Contract Reasoning: is_prime_simple

## Source Semantics

The raw function takes one integer `n` and returns `1` exactly when `n` is prime, otherwise `0`.

The problem statement fixes the input domain to `n >= 0`. A prime is an integer greater than `1` with no positive divisors other than `1` and itself.

The implementation:

- returns `0` immediately when `n < 2`
- scans candidate divisors `d` from `2` up to `n - 1`
- returns `0` immediately when `n % d == 0`
- returns `1` only after all candidate divisors have been excluded

## Boundary Cases

- `n = 0` and `n = 1`: not prime, so return `0`.
- `n = 2`: the loop body is skipped and the function returns `1`.
- `n > 2`: the result depends on whether some `d` with `2 <= d < n` divides `n`.

The loop increment is safe for all C `int` inputs satisfying the precondition: the final increment can bring `d` from `n - 1` to `n`, and no increment beyond `n` is required by the loop.

## Memory

The function is scalar-only. It reads no heap memory, writes no heap memory, and allocates nothing. The contract therefore uses `emp` in both precondition and postcondition.

## Specification Shape

The postcondition directly states the two allowed return cases:

- return `1` implies `2 <= n@pre` and no divisor exists in the scanned range
- return `0` implies either `n@pre < 2` or an in-range divisor exists

This matches the raw algorithm and avoids introducing any Verify-stage annotations such as loop invariants, assertions, bridge assertions, or loop-exit assertions.

## Coq Dependency Judgment

No `input/is_prime_simple.v` is needed. The prime predicate is simple enough to express directly in the C contract using `forall`, `exists`, arithmetic comparisons, and `%`.
