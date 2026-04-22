# Proof Reasoning

## 2026-04-20 Retry: first manual proof pass

After successful `symexec`, `coq/generated/min_cost_two_steps_proof_manual.v` contains seven admitted lemmas:

- `proof_of_min_cost_two_steps_safety_wit_4`: overflow safety for `cost[0] + cost[1]`;
- `proof_of_min_cost_two_steps_safety_wit_8`: overflow safety for `prev1 + cost[i]` in the `prev1 < prev2` branch;
- `proof_of_min_cost_two_steps_safety_wit_9`: overflow safety for `prev2 + cost[i]` in the `prev1 >= prev2` branch;
- `proof_of_min_cost_two_steps_entail_wit_1`: invariant initialization;
- `proof_of_min_cost_two_steps_entail_wit_2_1`: invariant preservation in the `prev1 < prev2` branch;
- `proof_of_min_cost_two_steps_entail_wit_2_2`: invariant preservation in the `prev1 >= prev2` branch;
- `proof_of_min_cost_two_steps_return_wit_2`: loop exit return condition.

The generated files compile successfully while those lemmas are admitted, so the first true blocker is replacing the manual admits. The first pass will try the standard skeleton `pre_process; entailer!; try lia` for each lemma. Expected remaining blockers are pure list facts about `sublist`, `sum`, `Znth`, and the recurrence in `min_cost_two_steps_z`; if those fail, the next step is to add local helper lemmas in `proof_manual.v` and keep each witness proof short.

## 2026-04-20 Retry: helper lemmas for prefix recurrence and sum bounds

The first compile after replacing all admits with `pre_process; entailer!; try lia` failed at `proof_of_min_cost_two_steps_safety_wit_4`, line 25, with open pure goals:

- `-2147483648 <= Znth 0 l 0 + Znth 1 l 0`;
- `Znth 0 l 0 + Znth 1 l 0 <= 2147483647`.

The context has nonnegative element facts and `sum l <= INT_MAX`, but Coq needs explicit bridges: first two elements form the length-2 prefix sum, nonnegative prefixes are bounded by the full sum, and the DP prefix recurrence follows from appending a singleton to an already-length-at-least-2 prefix. I tested the core recurrence helpers in `coqtop`: `min_cost_acc_snoc`, `min_cost_acc_prefix_prev`, `min_cost_prev_acc_prefix`, and `min_cost_two_steps_z_snoc`. Next edit adds these helpers plus sum-prefix helpers directly to `proof_manual.v`, then rewrites the witness proofs to call them rather than relying on automation.

## 2026-04-20 Retry: unresolved blocker

Latest compile of `coq/generated/min_cost_two_steps_proof_manual.v` still fails in `proof_of_min_cost_two_steps_entail_wit_1`. The intended proof was to rewrite `sublist 0 1 l` and `sublist 0 2 l` into singleton/two-element prefixes, then simplify `min_cost_two_steps_z`. However, after `pre_process; entailer!; try lia`, the first remaining focused goal is not stable under the current bullet script: Coq reports a unification error around line 240, where the script expects the singleton-prefix equality but the active goal mentions `sum (sublist 0 2 l)` versus `Znth 0 l 0 + Znth 1 l 0`.

Work completed before this blocker: `symexec` succeeds; helper lemmas for DP prefix-snoc and nonnegative prefix-sum bounds were added and earlier proof failures were advanced. Next retry should first inspect the exact proof state of `proof_of_min_cost_two_steps_entail_wit_1` after `pre_process; entailer!` and then rewrite that lemma with explicit `unfold min_cost_two_steps_entail_wit_1; intros; entailer!` bullets rather than relying on the current brittle bullet order.

## 2026-04-20 Retry: exact entailment blocker state

I inspected `proof_of_min_cost_two_steps_entail_wit_1` with `coqtop` after `pre_process; entailer!; try lia`. The remaining goals are, in order: `(Znth 0 l 0 + Znth 1 l 0) <= sum (sublist 0 2 l)`, nonnegativity of the same sum, `Znth 0 l 0 <= sum (sublist 0 (2 - 1) l)`, nonnegativity of `Znth 0 l 0`, and the two semantic equalities for `min_cost_two_steps_z` on `sublist 0 2 l` and `sublist 0 (2 - 1) l`. The previous bullet order tried to prove the singleton semantic equality first, so line 240 ran `reflexivity` against the first prefix-sum goal and failed with `Unable to unify "sum (sublist 0 2 l)" with "Znth 0 l 0 + Znth 1 l 0"`.

The next proof edit will add small local helper lemmas describing the shape of `sublist 0 1 l` and `sublist 0 2 l` under the known length bounds, then rewrite `proof_of_min_cost_two_steps_entail_wit_1` in the actual generated subgoal order. This preserves the existing DP recurrence and sum-bound helpers and only repairs the current blocker.

## 2026-04-20 Retry: helper side-condition repair

The first compile after adding prefix-shape helpers failed at `sublist_0_1_by_Znth`, line 162, with `Cannot find witness`. The local `sublist_single` lemma from `AUXLib.ListLib` quantifies over an explicit default element and uses `Z.of_nat (length l)` in its side condition, while the current context only had `Zlength l`. The repair is to instantiate `sublist_single` explicitly with default `0` and expose `Zlength_correct l` before `lia` handles the bound.

The next compile advanced to `sublist_0_2_by_Znth`, line 171, with the same `Cannot find witness` side-condition issue on `sublist_split` / `sublist_single`. I will expose `Zlength_correct l` in that helper too and instantiate the second singleton rewrite explicitly with default `0`.

## 2026-04-20 Retry: live compile blocker at sublist_0_2_by_Znth

The current manual compile fails in `coq/generated/min_cost_two_steps_proof_manual.v` line 171 with `Error: Tactic failure: Cannot find witness.` The failing command is `rewrite (sublist_split 0 2 1 l) by lia` inside `sublist_0_2_by_Znth`. This is not a new semantic blocker: the side condition needs `Zlength_correct l` exposed so that `lia` can relate `Zlength l` to the nat length form used by the list lemma. Next edit keeps all witness proofs unchanged and only adds the missing explicit length fact in this helper before the rewrite.

## 2026-04-20 Retry: brittle generated hypothesis names in loop preservation

After repairing the prefix-shape helper, the compile advanced to `proof_of_min_cost_two_steps_entail_wit_2_1` line 277 with `Error: No such assumption.` The failing subgoal is the preserved `prev1 = min_cost_two_steps_z (sublist 0 ((i_2 + 1) - 1) l)` equality after rewriting `((i_2 + 1) - 1)` to `i_2`. The previous proof used a bare `assumption`, but `pre_process`/`entailer!` does not leave the exact equality in a form that `assumption` picks up reliably. Next edit replaces those bare assumptions in both loop-preservation branches with explicit `match goal` selections for the invariant equality or bound, leaving the semantic recurrence proof unchanged.

## 2026-04-20 Retry: actual loop-preservation subgoal order

`coqtop` showed that after `pre_process; entailer!; try lia` in `proof_of_min_cost_two_steps_entail_wit_2_1`, the remaining goals are not the invariant clauses in source order. The first goal is the separation-logic permission `&( "cur") # Int |-> ... |-- &( "cur") # Int |->_`, followed by the new-prefix sum upper bound, nonnegativity, preserved `prev1` sum bound, the DP recurrence, and only then the preserved `prev1` semantic equality. The previous script addressed the preserved equality first, causing the match failure. Next edit reorders both branch proofs to solve the heap goal with `entailer!` first and then handle the pure goals in this observed order.

## 2026-04-20 Retry: stale equality name inside recurrence rewrite

After solving the `cur` heap-permission goal with `store_int_undef_store_int`, the compile advanced to the recurrence bullet and failed at line 292 with `Found no subterm matching "prev2" in the current goal.` In the actual `coqtop` context, `H5` is `0 <= prev2`; the semantic equality for `prev2` is `H3`, while `H4` is the semantic equality for `prev1`. The next edit changes both branch recurrence bullets from rewriting with `H5` to rewriting with `H3`.

## 2026-04-20 Retry: abstract prefix-snoc recurrence helper

The recurrence bullet is fragile when it tries to rewrite `sublist 0 (i_2 + 1) l` inline. The stable statement needed by both loop branches is: for `2 <= i < Zlength l`, `min_cost_two_steps_z (sublist 0 (i + 1) l)` equals `Z.min` of the two previous prefix DP values plus `Znth i l 0`. This follows from `sublist_split`, `sublist_single`, `min_cost_two_steps_z_snoc`, and `sublist_sublist00`. Next edit adds this as a helper lemma and simplifies the two recurrence bullets to call it.

## 2026-04-20 Retry: return witness rewrite made explicit

The compile advanced to `proof_of_min_cost_two_steps_return_wit_2` and failed at `rewrite H12 in H4` with setoid-rewrite unresolved evars. `coqtop` shows the post-`entailer!` goal is simply `prev1 = min_cost_two_steps_z l`, with a loop-exit arithmetic fact implying `i_2 = n_pre`, a semantic invariant `prev1 = min_cost_two_steps_z (sublist 0 i_2 l)`, and a length invariant `Zlength l = n_pre`. The next edit avoids rewriting inside a hypothesis; it substitutes `i_2`, rewrites the goal with the semantic invariant, and uses `sublist_self` after rewriting the length on the goal side.
