## 2026-04-21 03:48:43 CST - initial loop invariant for fibonacci_mod

Program point: the `for (i = 2; i <= n; ++i)` loop in `annotated/verify_20260421_034752_fibonacci_mod.c`.

The input contract says the result must equal `fib_mod_z(n@pre, mod@pre)`. The helper definition `fib_mod_z n m` is `fst (fib_mod_pair (Z.to_nat n) m)`, where `fib_mod_pair 0 m = (0, 1 rem m)` and one step maps `(x, y)` to `(y, (x + y) rem m)`.

Before the loop starts in the nonzero branch, the C variables are `a = 0`, `b = 1 % mod`, and the next loop index is `i = 2`. At that control point, `(a, b)` should represent `fib_mod_pair 0 mod`, which is the pair needed before computing index 2. More generally, at the loop judgment point for index `i`, the current pair should represent `fib_mod_pair (i - 2) mod`: executing one loop body computes `c = (a + b) % mod`, then shifts `a = b` and `b = c`, matching one `fib_mod_pair` step. After the loop exits, `i > n` with the invariant bound should give `i = n + 1`, so `(a, b)` represents `fib_mod_pair (n - 1) mod`; the returned `b` is the second component of that pair, which is definitionally the first component after one more step, i.e. `fib_mod_z n mod`.

The invariant must also preserve `n == n@pre` and `mod == mod@pre`, because the postcondition uses pre-state parameters. I will add bounds `2 <= i && i <= n + 1`, the two parameter-stability facts, the pair relation for `a` and `b`, and `emp`.

## 2026-04-21 03:49:18 CST - rewrite invariant to parser-supported function form

The first `symexec` run failed during annotation parsing before meaningful VC generation:

`bison: syntax error, unexpected PT_IDENT, expecting PT_RPAREN or PT_COMMA in annotated/verify_20260421_034752_fibonacci_mod.c:30:55`.

The failing text was the direct Coq projection/application form `fst (fib_mod_pair (Z.to_nat (i - 2)) mod)`. Existing annotated examples use front-end function-call syntax such as `power_nonnegative_z(base, i)`, not raw Coq application syntax inside C annotations. Since the input C already exports `fib_mod_z`, I will express the loop state as:

- `a == fib_mod_z(i - 2, mod)`
- `b == fib_mod_z(i - 1, mod)`

This keeps the same control-point meaning without requiring projection syntax in the annotation parser. I will also add `0 <= a && a < mod` and `0 <= b && b < mod`, because the loop body computes `a + b`; with `mod <= 1073741824`, these facts give `a + b <= 2147483646`, which is the needed signed-int safety bound.
