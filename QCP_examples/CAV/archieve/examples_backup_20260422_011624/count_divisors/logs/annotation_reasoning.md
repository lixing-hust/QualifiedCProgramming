## 2026-04-21 02:06:24 +0800

Initial annotated copy has no loop invariant, but the function contains a `for (d = 1; d <= n; ++d)` loop and the postcondition requires `cnt` to equal `count_divisors_spec(n@pre)`. At the loop condition point, `d` is the next divisor candidate to inspect, so the processed range is `1..d-1`. The accumulator `cnt` should therefore be tied to the Coq helper `count_divisors_upto n (Z.to_nat (d - 1))`.

The invariant should preserve `n == n@pre`, because the final Ensure mentions `n@pre` while the loop body only reads the local `n`. Bounds should be `1 <= d && d <= n + 1`: initialization gives `d == 1`, each successful body execution advances by one, and loop exit from `d <= n` should give `d == n + 1`. With the accumulator expression above, initialization reduces to `count_divisors_upto n (Z.to_nat 0) == 0`, and the preservation step corresponds to the recursive definition deciding whether `n % d == 0`.

I will add this invariant immediately before the `for` loop. I will also add a minimal loop-exit `Assert` immediately after the loop to expose `d == n + 1`, preserve `n == n@pre`, and bridge the accumulator to `count_divisors_spec(n)` for the return witness.

## 2026-04-21 02:07:13 +0800

The first `symexec` run reached the function body but failed before VC generation with `Use of undeclared identifier 'count_divisors_upto'` at the invariant line. The current input V already defines `count_divisors_upto`, and the annotated file already imports `count_divisors`, but only `count_divisors_spec` was declared via `Extern Coq`. The invariant needs the prefix helper because `count_divisors_spec(n)` describes only the full range `1..n`, not the partial range processed at loop head.

I will add a second `Extern Coq` declaration for the already-provided helper `count_divisors_upto : Z -> nat -> Z` in the annotated working copy, leaving `Require` and `Ensure` unchanged. Then I will clear the partial generated files and rerun `symexec`.

## 2026-04-21 02:07:50 +0800

After exposing `count_divisors_upto`, the next `symexec` run failed at the same invariant with `Use of undeclared identifier 'Z'`, caused by the annotation expression `Z.to_nat(d - 1)`. This is a frontend parsing limitation: the invariant needs a prefix-count function, but the C annotation parser is not accepting the module-qualified Coq function name.

I will avoid module-qualified syntax in the C annotation by introducing a workspace-local Coq helper `count_divisors_prefix (n limit : Z) := count_divisors_upto n (Z.to_nat limit)` under `coq/deps/`. The annotated C will import that helper and use `count_divisors_prefix(n, d - 1)`. This preserves the original Require/Ensure while giving symexec a parser-friendly pure function name.
