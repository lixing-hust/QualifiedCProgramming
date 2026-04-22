# Proof Reasoning

## Round 1

- Read `array_adjacent_diff_goal.v`, `array_adjacent_diff_proof_auto.v`, and `array_adjacent_diff_goal_check.v`.
- The generated `proof_manual.v` contains five unfinished lemmas:
  - `proof_of_array_adjacent_diff_safety_wit_4`
  - `proof_of_array_adjacent_diff_entail_wit_1`
  - `proof_of_array_adjacent_diff_entail_wit_2`
  - `proof_of_array_adjacent_diff_entail_wit_3`
  - `proof_of_array_adjacent_diff_return_wit_1`
- Initial classification:
  - `safety_wit_4` is pure arithmetic and should discharge from the contract’s adjacent-difference range hypothesis.
  - `entail_wit_1` is the invariant initialization witness and should use the empty processed prefix.
  - `entail_wit_2` is the loop-step witness; this is the only place that needs nontrivial list normalization for `replace_Znth` on `app(l1, sublist(i, ...))`.
  - `entail_wit_3` is the loop-exit witness and should reduce to `i = n_pre - 1` plus `sublist_nil`.
  - `return_wit_1` should be a direct existential instantiation with the already available `lr_2`.
- Reused pattern source: `examples/array_add/coq/generated/array_add_proof_manual.v`, especially the proof style for an output-prefix extension after one array write.

## Round 2

- First stable compile failure: `compile_proof_manual.log` reported `Cannot find witness` inside the local helper lemma `adjacent_diff_step_list`, at the `sublist_split` rewrite.
- Diagnosis: the rewrite side conditions depend on `Zlength lo = n - 1`, but that equality was still implicit in `Hlo`; the generic `lia` call did not expose it in the exact form required by the library lemma.
- Next change: rewrite with `Hlo` before `sublist_split` and `sublist_single` so the side conditions are stated directly over `Zlength lo`.

## Round 3

- The previous adjustment was too aggressive: `compile_proof_manual.log` then failed with `Found no subterm matching "Zlength lo"`, so there was no direct rewrite site for `Hlo` in the goal term itself.
- The real need is narrower: `Hlo` only has to be used inside the side-condition proofs for `sublist_split` and `sublist_single`.
- Next change: keep the goal term untouched and pass `rewrite Hlo; lia` only in those side-condition branches.

## Round 4

- That still failed because the underlying `sublist` lemmas in this library are phrased over `length`, not `Zlength`.
- So the missing bridge is `rewrite Zlength_correct in Hlo` inside those side-condition proofs, not a direct rewrite on the goal term.

## Round 5

- The next compile blocker is parser-level again: this Coq version rejected `induction l1 as [|x xs IH]`.
- Fix: switch that helper proof to the conservative style `induction l1.` with the induction hypothesis name produced by the environment.

## Round 6

- After the syntax fix, the helper still failed because the local `assert` proof mixed induction focus with the surrounding proof script.
- This is unnecessary complexity: the library already provides `replace_Znth_nothing`, which directly states that replacing at index `Zlength l1` leaves `l1` unchanged.
- Next change: remove the local induction entirely and use `rewrite replace_Znth_nothing by lia`.

## Round 7

- The helper now reaches the final equality, but `reflexivity` is still too weak because the goal is stuck at:
  - `l1 ++ replace_Znth 0 diff (Znth i lo 0 :: sublist ...)`
  - versus `(l1 ++ diff :: nil) ++ sublist ...`
- This is just normalization of the head write plus append associativity.
- Next change: after rewriting away the prefix update, explicitly `simpl`, rewrite `app_assoc`, and finish by reflexivity.

## Round 8

- The next compile failure was in `proof_of_array_adjacent_diff_safety_wit_4`: the `pre_process`-generated hypothesis names did not match the script (`H10` was absent).
- To remove that instability, I am rewriting this witness with `unfold ...; intros ...` so the adjacent-difference bound hypothesis is named explicitly.

## Round 9

- The unfolded form was too raw for this generated proposition shape (`No product even after head-reduction`), so fully manual intros are not the right entry point here.
- Better approach: keep `pre_process` and locate the needed adjacent-difference bound hypothesis by structure with `match goal`, not by a fragile generated name.

## Round 10

- `proof_of_array_adjacent_diff_entail_wit_1` then failed with an incomplete proof.
- The missing step is the initialization normalization `app nil (sublist 0 (n_pre - 1) lo) = lo`, which requires explicitly rewriting `n_pre - 1` to `Zlength lo` and then applying `sublist_self`.

## Round 11

- `entail_wit_2` needed proof-state inspection with `coqtop`.
- After `entailer!`, the remaining goals are in this order:
  1. the prefix pointwise property
  2. the `Zlength` equality
- The script had them reversed, which is why the first bullet tried to rewrite `Zlength` in the wrong goal.

## Round 12

- `entail_wit_3` also needed `coqtop`.
- After `entailer!`, the residual goals are:
  1. a small separation-logic entailment dropping the local `n` store
  2. the final prefix property
- So the proof needs `cancel` first, then the pure `forall` argument reusing `H5` together with `H10 : Zlength l1 = n_pre - 1`.

## Round 13

- That local-store entailment was a signal that the loop-exit assertion itself was mispositioned for this verifier.
- I removed the exit assertion, cleared the generated Coq files, and reran `symexec`.
- The regenerated `proof_manual.v` became smaller:
  - `safety_wit_4`
  - `entail_wit_1`
  - `entail_wit_2`
  - `return_wit_1`
- The problematic loop-exit entailment disappeared completely.

## Round 14

- Rebuilt `proof_manual.v` against the regenerated VC using:
  - the same `adjacent_diff_step_list` helper for the loop step
  - direct initialization normalization for `entail_wit_1`
  - direct loop-exit-to-postcondition reasoning in `return_wit_1`
- Final compile replay status:
  - `array_adjacent_diff_goal.v` compiles
  - `array_adjacent_diff_proof_auto.v` compiles
  - `array_adjacent_diff_proof_manual.v` compiles
  - `array_adjacent_diff_goal_check.v` compiles
- `array_adjacent_diff_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`.
