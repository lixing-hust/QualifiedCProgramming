## 2026-04-20 annotation pass 1

Current state: `annotated/verify_20260420_221428_tribonacci.c` is identical to `input/tribonacci.c`, so the `for (i = 3; i <= n; ++i)` loop has no invariant. This will block `symexec` at the loop because the verifier has no persistent relationship between the rolling scalar variables and the imported specification function `tribonacci_z`.

Program point: immediately before the loop. At that point, after the early returns for `n == 0` and `n == 1`, the path condition gives `2 <= n <= 37`, and the initialized variables are `a = 0`, `b = 1`, `c = 1`, `i = 3`. These match `tribonacci_z(0)`, `tribonacci_z(1)`, and `tribonacci_z(2)` under the intended imported Coq definition.

Planned annotation: add a loop invariant before the `for` statement stating `3 <= i && i <= n + 1`, `n == n@pre`, `a == tribonacci_z(i - 3)`, `b == tribonacci_z(i - 2)`, `c == tribonacci_z(i - 1)`, and `emp`. This mirrors the existing verified Fibonacci pattern but with three rolling accumulators. Initialization should hold at `i = 3`; preservation follows because the loop body computes `d = a + b + c` then shifts `(a,b,c)` to `(b,c,d)`; and on exit, `i == n + 1` should make `c == tribonacci_z(n)`, matching the return postcondition.
