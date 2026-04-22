## Initial loop invariant plan

Program point: the only loop is `while (n > 0)` in `annotated/verify_20260421_022514_digit_sum.c`. The initial annotated file matches the contract input and has no `Inv`, so symbolic execution would lack a stable relation between the original input `n@pre`, the shrinking loop variable `n`, and the accumulator `sum`.

The target postcondition is `__return == digit_sum_z(n@pre) && emp`. At loop entry, `sum` is the digit sum of the already stripped low-order digits, and `n` is the unprocessed high-order quotient. The useful semantic invariant is therefore `sum + digit_sum_z(n) == digit_sum_z(n@pre)`. Initialization holds because `sum == 0` and `n == n@pre`. Preservation follows from the loop body under `n > 0`: the body adds `n % 10` to `sum` and replaces `n` by `n / 10`, matching the recursive step in `digit_sum_z`.

The arithmetic side of the invariant must also support C integer safety for `sum += n % 10`. I will keep `0 <= n`, `0 <= sum`, `n <= INT_MAX`, and `sum + n <= n@pre`. Under `n > 0`, the next accumulator satisfies `sum + n % 10 <= sum + n <= n@pre <= INT_MAX`, and the next `n / 10` remains nonnegative and bounded. This avoids pushing a missing overflow fact into manual proof.

The loop exit condition `!(n > 0)` combined with `0 <= n` gives `n == 0`. I will add a minimal loop-exit `Assert` immediately after the loop fixing `n == 0` and `sum == digit_sum_z(n@pre)`, so the return witness has the exact postcondition shape and does not have to rediscover the exit-state rewrite.
