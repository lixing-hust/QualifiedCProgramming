## Initial loop invariant plan

Program point: the only loop is `while (n > 0)` in `annotated/verify_20260421_050526_reverse_digits.c`. The current annotated file has no `Inv`, so symbolic execution has no loop-head summary relating the shrinking `n`, the accumulator `ans`, and the original pre-state value `n@pre`.

The postcondition is `__return == reverse_digits_z(n@pre) && emp`. At a loop head, `ans` is the reversed sequence of low-order digits already removed from the original input, while `n` is the remaining high-order quotient. The input Coq file already models exactly this state as `reverse_digits_fuel n acc fuel`, but a direct annotation with `Z.to_nat(n)` would be rejected by the C annotation frontend, as seen in the nearby `count_divisors` verify task. I will therefore add a workspace-local helper `reverse_digits_acc_z(n, acc) := reverse_digits_fuel n acc (Z.to_nat n)` in `coq/deps/reverse_digits_verify_aux.v`, import it only from the annotated working copy, and use `reverse_digits_acc_z(n, ans) == reverse_digits_z(n@pre)` as the core invariant.

The invariant also needs integer safety facts for `ans = ans * 10 + n % 10`: keep `0 <= n`, `n <= INT_MAX`, `0 <= ans`, `ans <= reverse_digits_z(n@pre)`, and `reverse_digits_z(n@pre) <= INT_MAX`. Under `n > 0`, the next accumulator is still nonnegative and should remain no larger than the final value represented by the helper relation, while `n / 10` stays nonnegative and bounded.

On loop exit, `0 <= n` and `!(n > 0)` imply `n == 0`; the helper unfolds to `reverse_digits_acc_z(0, ans) == ans`. I will add a minimal loop-exit `Assert` immediately after the loop fixing `n == 0`, preserving the final-bound fact, and bridging `ans == reverse_digits_z(n@pre)` for the return witness.
