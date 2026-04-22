# Verification Issues

## Issue 1: initial annotated loop had no invariant

- Phenomenon: `annotated/verify_20260421_052410_count_digits.c` initially matched the contract input and had no `Inv` for `while (n > 0)`.
- Trigger: `count_digits` mutates `n` by division and accumulates `cnt`, while the postcondition refers to `count_digits_z(n@pre)`.
- Location: `annotated/verify_20260421_052410_count_digits.c`, loop before the final `return cnt;`.
- Fix: added a loop invariant with scalar bounds, `cnt + n <= n@pre`, and a split semantic relation: if the current `n` is positive then `cnt + count_digits_z(n) == count_digits_z(n@pre)`, and if current `n` is zero then `cnt == count_digits_z(n@pre)`. Added a minimal loop-exit assertion fixing `n == 0` and the return relation.
- Result: `symexec` succeeded and generated fresh `count_digits_goal.v`, `count_digits_proof_auto.v`, `count_digits_proof_manual.v`, and `count_digits_goal_check.v`.

## Issue 2: direct `Z.eqb_neq` rewrite did not match unfolded `count_digits_z`

- Phenomenon: the first full Coq compile failed in `count_digits_proof_manual.v` with `Found no subterm matching "(?z =? ?z0) = false" in the current goal`.
- Trigger: helper lemmas unfolded `count_digits_z` and tried to use `rewrite Z.eqb_neq by lia`.
- Location: `coq/generated/count_digits_proof_manual.v`, helper lemmas `count_digits_fuel_stable_ge`, `count_digits_z_step_zero`, and `count_digits_z_step_pos`.
- Fix: replaced the rewrite with explicit `destruct (n =? 0)` branches and closed the impossible branch via `Z.eqb_eq` and `lia`.
- Result: the helper lemmas advanced to the next proof obligation.

## Issue 3: positive-step helper needed an explicit fuel-stability replacement

- Phenomenon: compiling `count_digits_z_step_pos` failed because Coq could not unify the helper conclusion with the goal under `1 + ...`.
- Trigger: `f_equal` left a concrete `Z` addition match term, and the stable-fuel lemma had the opposite equality orientation for the generated subterm.
- Location: `coq/generated/count_digits_proof_manual.v`, lemma `count_digits_z_step_pos`.
- Fix: replaced the recursive fuel call explicitly with `count_digits_z (n ÷ 10)`, used `symmetry; apply count_digits_fuel_stable_ge`, and supplied the fuel bound using `Z.of_nat k = n - 1` plus `quot_10_lt_pos`.
- Result: the positive-step helper compiled.

## Issue 4: loop-preservation arithmetic bullet needed quotient bounds

- Phenomenon: the manual witness compile failed with `Tactic failure: Cannot find witness`, then after adding the missing bound failed once with `Wrong bullet -: No more goals`.
- Trigger: one arithmetic side condition from `count_digits_entail_wit_2` required explicit facts about `n ÷ 10`; after adding them, a trailing bullet remained even though `entailer!` had solved the final nonnegative quotient condition.
- Location: `coq/generated/count_digits_proof_manual.v`, lemma `proof_of_count_digits_entail_wit_2`.
- Fix: added `pose proof (quot_10_lt_pos n ...)` for the quotient-bound side condition and removed the extra trailing bullet.
- Result: `proof_manual.v` compiled, and the final `count_digits_goal_check.v` compile passed.
