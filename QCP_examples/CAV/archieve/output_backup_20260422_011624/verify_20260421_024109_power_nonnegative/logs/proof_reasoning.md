## 2026-04-21 manual proof plan after first symexec

Fresh `symexec` succeeded on the current annotated file and generated three manual obligations in `coq/generated/power_nonnegative_proof_manual.v`: `proof_of_power_nonnegative_safety_wit_3`, `proof_of_power_nonnegative_entail_wit_1`, and `proof_of_power_nonnegative_entail_wit_2`.

The current blockers are pure arithmetic/definition obligations, not missing heap shape. `safety_wit_3` must show that `ans * base_pre` is in signed int range during the loop body. The available facts include `ans = power_nonnegative_z base_pre i`, `0 <= i`, `i < exp_pre`, and the contract's quantified overflow guard for every `k` with `0 <= k <= exp_pre`. This should be discharged by instantiating the guard at `i + 1` after proving the helper fact `power_nonnegative_z base (i + 1) = power_nonnegative_z base i * base`.

`entail_wit_1` is invariant initialization and should reduce to the definition of `power_nonnegative_z base 0 = 1`. `entail_wit_2` is loop preservation and needs the same successor helper lemma plus linear arithmetic for the updated index bounds.

Next edit: add a local helper lemma in `proof_manual.v` for the successor equation of `power_nonnegative_z` on nonnegative exponents, then replace the three `Admitted.` bodies with conservative `pre_process; entailer!` proofs that use this helper and `lia`.

## 2026-04-21 helper binder parse failure

First compile attempt failed in `coq/generated/power_nonnegative_proof_manual.v` at line 30 with: `The term "exp" has type "(?A -> model -> Prop) -> model -> Prop" while it is expected to have type "Z".`

This happened inside the local helper lemma, not inside a generated witness. Because `Local Open Scope sac` is active, the binder name `exp` collided with the separation-logic existential notation/function named `exp`. The next edit is to rename the helper lemma's exponent binder from `exp` to `e`, leaving the witness structure unchanged.

## 2026-04-21 entailment initialization over-proved

Second compile attempt failed in `proof_of_power_nonnegative_entail_wit_1` at `power_nonnegative_proof_manual.v:54` with `Error: No such goal.` The proof ran `pre_process` and then attempted `entailer!; unfold power_nonnegative_z; reflexivity`, but the initialization witness was already closed before the explicit rewrite. The next edit is to leave this witness at the shorter `pre_process.` proof and rerun the compile chain.
