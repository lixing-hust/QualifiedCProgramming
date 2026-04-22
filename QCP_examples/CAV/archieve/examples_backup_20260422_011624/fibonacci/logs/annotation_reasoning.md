## Iteration 1: consecutive Fibonacci accumulator invariant

The initial annotated file has no invariant for the `for (i = 2; i <= n; ++i)` loop.
That loop is the only place where the implementation accumulates the Fibonacci state, so verification needs a guard-point invariant that records exactly what the two accumulators mean.

Program point:

- active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_215456_fibonacci.c`
- target loop: the `for` loop after the `if (n == 0) return 0;` branch
- current variables at the first guard check: `i == 2`, `a == 0`, `b == 1`

The postcondition requires `__return == fib_z(n@pre)`.
After the early return branch is skipped, the pure facts include `n != 0`, `0 <= n`, and `n <= 46`, so the loop case has `1 <= n`.

Invariant design:

- preserve the parameter relation `n == n@pre`
- keep the loop index at the guard point with `2 <= i && i <= n + 1`
- represent the accumulator pair as consecutive Fibonacci values:
  - `a == fib_z(i - 2)`
  - `b == fib_z(i - 1)`

Initialization:

- before the first guard check, `i == 2`, `a == 0`, and `b == 1`
- `fib_z(0) == 0` and `fib_z(1) == 1` should match the accumulator values
- because the zero case already returned, `n >= 1`, so `2 <= n + 1`

Preservation:

- at a loop-body entry, the guard gives `i <= n`
- `c = a + b` computes the next Fibonacci value from the two consecutive values
- after `a = b`, `b = c`, and `++i`, the next guard state should satisfy the same invariant with index `i + 1`

Exit:

- the negated guard gives `i > n`
- together with `i <= n + 1`, this yields `i == n + 1`
- then `b == fib_z(i - 1)` becomes `b == fib_z(n)`, and `n == n@pre` gives the required postcondition

I will first add only this invariant and no separate loop-exit assertion. If `symexec` shows that the return witness cannot derive `i == n + 1` or `b == fib_z(n@pre)`, the next annotation iteration should add a minimal assertion immediately after the loop.
