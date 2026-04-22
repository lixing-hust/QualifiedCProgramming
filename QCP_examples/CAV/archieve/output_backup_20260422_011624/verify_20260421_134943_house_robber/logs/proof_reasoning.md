# Proof Reasoning

## 2026-04-21 manual obligations after successful symexec

Fresh `symexec` succeeded for `annotated/verify_20260421_134943_house_robber.c` and generated five manual obligations in `coq/generated/house_robber_proof_manual.v`:

- `proof_of_house_robber_safety_wit_4`: overflow bound for `prev2 + Znth i l 0` before assigning `take`.
- `proof_of_house_robber_entail_wit_1`: loop invariant initialization at `i == 0`.
- `proof_of_house_robber_entail_wit_2_1`: invariant preservation for the `take > prev1` branch.
- `proof_of_house_robber_entail_wit_2_2`: invariant preservation for the `take <= prev1` branch.
- `proof_of_house_robber_return_wit_1`: loop exit bridge from `prev1 == house_robber_spec(sublist 0 i l)` and `i == n` to `prev1 == house_robber_spec(l)`.

The current available hypotheses include nonnegative elements over `0 <= i < n_pre`, `Zlength l = n_pre`, `sum l <= INT_MAX`, the loop bounds, and the invariant equalities for `prev1` and `prev2`. A bare `pre_process; entailer!; try lia` will not be enough for the branch-preservation witnesses because the proof must expose the Coq recurrence:

`house_robber_spec(sublist 0 (i + 1) l) = Z.max (house_robber_spec(sublist 0 (i - 1) l) + Znth i l 0) (house_robber_spec(sublist 0 i l))`.

Plan: add helper lemmas directly in `house_robber_proof_manual.v` for the previous accumulator over prefixes, the snoc recurrence, nonnegative prefix sums, and prefix-sum bounds. Then keep the witness proofs short: `pre_process`, solve heap changes with `store_int_undef_store_int` where needed, use the recurrence helper for the two branch witnesses, and use `sublist_self` for the final return witness.

## 2026-04-21 first compile failure in helper lemma

Compile result: the first `coqc` run failed in `house_robber_spec_prev_prefix` at the `sublist_cons1` side condition with `Tactic failure: Cannot find witness.` The failing line used `pose proof Zlength_nonneg (z :: xs); lia`, which did not discharge the `1 <= n` premise expected by `sublist_cons1`.

Next proof change: rewrite the side-condition proof in the same explicit style as the existing `min_cost_two_steps` DP example, using repeated `Zlength_cons` rewrites and `Zlength_nonneg xs` so the arithmetic goal is directly visible to `lia`.

## 2026-04-21 second compile failure in previous-prefix helper

Compile result: after fixing the `sublist_cons1` side condition, `coqc` failed in `house_robber_spec_prev_prefix` with `Found no subterm matching "house_robber_acc 0 0 (...)"`. The induction hypothesis was too specialized to initial accumulators `0 0`; after consuming the head element, the recursive proof state has arbitrary updated accumulators.

Next proof change: replace the specialized helper with a general lemma `house_robber_acc_prev_prefix` quantified over `prev2` and `prev1`, then prove `house_robber_spec_prev_prefix` by unfolding `house_robber_spec` and applying the general lemma at `0 0`.

## 2026-04-21 third compile failure: empty-list accumulator corner

Compile result: the generalized previous-prefix lemma failed in the empty-list case with `Unable to unify "prev2" with "prev1"`. This is a real edge case: for an empty input, `house_robber_acc prev2 prev1 nil = prev1`, while `house_robber_prev_acc prev2 prev1 nil = prev2`. The lemma is only true for nonempty lists, except for the special `0 0` case used by `house_robber_spec`.

Next proof change: add a `1 <= Zlength xs` premise to the generalized helper, discharge the nil case by contradiction, and prove the specialized `house_robber_spec_prev_prefix` by destructing `xs`; the empty case is direct because both accumulators are zero.

## 2026-04-21 fourth compile failure: sublist_split length form

Compile result: `house_robber_spec_prefix_snoc` failed at `rewrite (sublist_split 0 (i + 1) i l) by lia` with `Cannot find witness`. The lemma `sublist_split` requires the upper bound in `Z.of_nat (length l)` form, while the local hypothesis is stated with `Zlength l`.

Next proof change: add `pose proof (Zlength_correct l)` before the split rewrite so `lia` can bridge the two length forms, matching the pattern used in the existing DP example.

## 2026-04-21 fifth compile failure: recurrence at i = 0

Compile result: `house_robber_spec_prefix_snoc` next failed at `sublist_sublist00 by lia`. This rewrite requires `0 <= i - 1`, which is false in the `i = 0` case. The generated invariant intentionally uses `sublist 0 (i - 1)` uniformly, so the proof needs to handle the first iteration separately.

Next proof change: split `house_robber_spec_prefix_snoc` on `i = 0`. For `i = 0`, both `sublist 0 (-1) l` and `sublist 0 0 l` are empty and the recurrence reduces directly to the one-element execution of `house_robber_acc`. For `i > 0`, keep the snoc proof and `sublist_sublist00` rewrite.

## 2026-04-21 sixth compile failure: prefix-sum split length form

Compile result: `sum_prefix_le_full_nonneg` failed at the `sublist_split` rewrite with another `Cannot find witness`. This is the same length-form mismatch as the recurrence helper: `sublist_split` needs `Z.of_nat (length l)` while the lemma uses `Zlength l`.

Next proof change: add `pose proof (Zlength_correct l)` before the prefix-sum split.

## 2026-04-21 seventh compile failure: prefix-sum snoc split length form

Compile result: `sum_prefix_snoc` failed at its `sublist_split` rewrite with `Cannot find witness`, again due to the missing `Zlength_correct l` bridge.

Next proof change: add `pose proof (Zlength_correct l)` at the start of `sum_prefix_snoc`.

## 2026-04-21 eighth compile failure: safety witness bullet order

Compile result: `proof_of_house_robber_safety_wit_4` failed after `pre_process; entailer!; try lia`. `coqtop` showed the remaining goals are ordered as:

1. `INT_MIN <= prev2 + Znth i l 0`
2. `prev2 + Znth i l 0 <= INT_MAX`

The previous proof handled the upper-bound argument first, so the prefix-sum rewrite was being applied to the lower-bound goal and the later `lia` had the wrong context.

Next proof change: swap the bullets. The first goal only needs `prev2 >= 0` and `Znth i l 0 >= 0`; the second goal uses `sum_prefix_snoc`, `sum_prefix_le_full_nonneg`, and `sum l <= INT_MAX`.

## 2026-04-21 ninth compile failure: initialization empty-prefix sums

Compile result: `proof_of_house_robber_entail_wit_1` failed with remaining goals after `pre_process; entailer!`. `coqtop` showed two identical goals `0 <= sum (sublist 0 0 l)`.

Next proof change: after `entailer!`, unfold `sublist` and simplify the empty prefix sums, then close them with `lia`.

## 2026-04-21 tenth compile failure: branch witness 2_1 subgoal order

Compile result: `proof_of_house_robber_entail_wit_2_1` failed because the first post-`entailer!` goal was not the recurrence equality. `coqtop` showed the remaining goals are ordered as:

1. `prev1 <= sum (sublist 0 (i_2 + 1) l)`
2. `prev2 + Znth i_2 l 0 <= sum (sublist 0 (i_2 + 1) l)`
3. `prev1 = house_robber_spec (sublist 0 (i_2 + 1 - 1) l)`
4. `prev2 + Znth i_2 l 0 = house_robber_spec (sublist 0 (i_2 + 1) l)`

Next proof change: reorder the bullets to solve the prefix-sum bounds first using `sum_prefix_snoc` and nonnegative `Znth`, then solve the simple previous-prefix equality, and only then use the recurrence helper for the final semantic equality.

## 2026-04-21 eleventh compile failure: recurrence equality orientation

Compile result: the final bullet of `proof_of_house_robber_entail_wit_2_1` reached `prev2 + Znth i_2 l 0 = Z.max (prev2 + Znth i_2 l 0) prev1`. The proof attempted `apply Z.max_l`, whose conclusion is oriented as `Z.max x y = x`.

Next proof change: add `symmetry` before applying `Z.max_l`.

## 2026-04-21 twelfth compile failure: branch witness 2_2 subgoal order

Compile result: `proof_of_house_robber_entail_wit_2_2` failed for the same reason as branch `2_1`: the first remaining goal after `entailer!` was a prefix-sum bound, not the recurrence equality. `coqtop` showed four goals:

1. `prev1 <= sum (sublist 0 (i_2 + 1) l)`
2. `prev1 <= sum (sublist 0 (i_2 + 1) l)`
3. `prev1 = house_robber_spec (sublist 0 (i_2 + 1 - 1) l)`
4. `prev1 = house_robber_spec (sublist 0 (i_2 + 1) l)`

Next proof change: solve the two duplicate prefix bounds using `sum_prefix_snoc` and nonnegative `Znth`, then solve the previous-prefix equality, then rewrite the recurrence and apply `Z.max_r` under the branch condition `prev2 + Znth i_2 l 0 <= prev1`.

## 2026-04-21 thirteenth compile failure: return witness setoid rewrite

Compile result: `proof_of_house_robber_return_wit_1` failed at `rewrite H11 in H2` with a setoid rewrite evar error. The intended step is only to replace `sublist 0 n_pre l` with `l`, but rewriting the length equality inside `house_robber_spec (sublist ...)` asks typeclass machinery for `Proper` instances that are not available.

Next proof change: avoid setoid rewriting. After deriving `i_2 = n_pre`, rewrite the goal with the invariant equality `H2`, then use `f_equal` plus `sublist_self` and the length equality to prove the argument lists are equal.

## 2026-04-21 final proof result

After the return-witness rewrite was changed to the `f_equal`/`sublist_self` proof, the complete compile replay succeeded for `original/house_robber.v`, `house_robber_goal.v`, `house_robber_proof_auto.v`, `house_robber_proof_manual.v`, and `house_robber_goal_check.v`.

Final manual proof state:

- `house_robber_proof_manual.v` contains no `Admitted.`.
- `house_robber_proof_manual.v` contains no top-level `Axiom`.
- The final `goal_check.v` compile passed with the workspace load path `SimpleC.EE.CAV.verify_20260421_134943_house_robber`.
