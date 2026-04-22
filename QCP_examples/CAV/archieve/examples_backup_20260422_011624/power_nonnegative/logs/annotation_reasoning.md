## 2026-04-21 initial loop invariant

Program point: the `for (i = 0; i < exp; ++i)` loop in `annotated/verify_20260421_024109_power_nonnegative.c`.

The unannotated loop loses the relationship between the accumulator `ans` and the mathematical function in the postcondition. At the loop guard, `i` represents the number of multiplications already performed, so the stable semantic fact should be `ans == power_nonnegative_z(base, i)`. The loop also needs `0 <= i && i <= exp`, because the contract's overflow guard is quantified over `0 <= k <= exp` and must be instantiated for the current iteration index before `ans * base`. The postcondition uses `base@pre` and `exp@pre`, so the invariant must preserve `base == base@pre` and `exp == exp@pre`.

Initialization: before the first guard check, `i == 0` and `ans == 1`, which matches `power_nonnegative_z(base, 0)` by the Coq definition.

Preservation: assuming `ans == power_nonnegative_z(base, i)` and `i < exp`, the body sets `ans` to the next power and then increments `i`, so the next guard state should satisfy `ans == power_nonnegative_z(base, i)` for the incremented `i`. Any remaining arithmetic about `power_nonnegative_z(base, i + 1)` may become a manual proof obligation.

Exit: when the loop exits, `0 <= i && i <= exp` plus `!(i < exp)` should yield `i == exp`, and then `ans == power_nonnegative_z(base, i)` plus the preserved pre-state equalities yields the return postcondition.
