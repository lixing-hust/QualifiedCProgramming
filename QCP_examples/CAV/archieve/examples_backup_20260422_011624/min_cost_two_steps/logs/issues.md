# Execution Issues

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_222721.log`

## Retry continuation: fingerprint and proof blocker

- Stage: `workspace-fingerprint`
- Phenomenon: `logs/workspace_fingerprint.json` still had an empty `semantic_description` and empty `keywords` at retry start.
- Trigger: retry rule required checking the fingerprint before continuing.
- Location: `output/verify_20260420_222721_min_cost_two_steps/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md` and filled `semantic_description` plus controlled-vocabulary `keywords` for a dynamic-programming array-preserving loop verification task.
- Result: fingerprint no longer has empty semantic fields.

- Stage: `symexec`, first annotated attempt
- Phenomenon: `symexec` failed with `Fail to Remove Memory Permission of cur:105`.
- Trigger: a post-loop `Assert` was placed after the `for` loop to force `i == n` and `prev1 == min_cost_two_steps_z(l)`.
- Location: `annotated/verify_20260420_222721_min_cost_two_steps.c`, assertion after the loop; log in `logs/qcp_run.log` from the first failed attempt.
- Fix action: removed only the post-loop assertion and kept the loop invariant.
- Result: rerunning `symexec` succeeded and regenerated `min_cost_two_steps_goal.v`, `min_cost_two_steps_proof_auto.v`, `min_cost_two_steps_proof_manual.v`, and `min_cost_two_steps_goal_check.v`.

- Stage: `proof_manual`
- Phenomenon: replacing all generated manual admits with `pre_process; entailer!; try lia` failed first at `proof_of_min_cost_two_steps_safety_wit_4`, then required helper lemmas for nonnegative prefix sums and the `min_cost_two_steps_z` prefix-snoc recurrence.
- Trigger: Coq could not infer that `Znth 0 l 0 + Znth 1 l 0` is bounded by `sum l`, nor that appending `Znth i l 0` to a prefix follows the DP recurrence.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`.
- Fix action: added local helpers `min_cost_two_steps_prev_acc`, `min_cost_acc_snoc`, `min_cost_acc_prefix_prev`, `min_cost_prev_acc_prefix`, `min_cost_two_steps_z_snoc`, `sum_nonneg_by_Znth`, `sum_prefix_le_full_nonneg`, and `sum_prefix_snoc`; completed several earlier safety proof steps.
- Result: proof did not complete. The current blocker is in `proof_of_min_cost_two_steps_entail_wit_1`: the proof script around line 239 is trying to rewrite `sublist 0 1 l` with a singleton, but the focused goal after `entailer!` is not the expected prefix-min-cost equality. Latest compile command fails in `min_cost_two_steps_proof_manual.v` around line 240 with a unification error involving `sum (sublist 0 2 l)` and `Znth 0 l 0 + Znth 1 l 0`.

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_225321.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_225414.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_225525.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_225931.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230003.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230034.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230105.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230137.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230208.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230240.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230312.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_222721_min_cost_two_steps/logs/codex_stderr_20260420_230344.log`

## Retry continuation completed by in-process repair

- Stage: `proof_manual`, helper side condition
- Phenomenon: compiling `min_cost_two_steps_proof_manual.v` failed at `sublist_0_2_by_Znth` with `Cannot find witness` on `rewrite (sublist_split 0 2 1 l) by lia`.
- Trigger: the `sublist_split` side condition uses the nat-length form internally, while the proof context only exposed `Zlength l`.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`, helper `sublist_0_2_by_Znth`.
- Fix action: added `pose proof (Zlength_correct l)` before the split rewrite.
- Result: helper compiled and proof advanced to loop-preservation witnesses.

- Stage: `proof_manual`, loop preservation subgoal ordering
- Phenomenon: `proof_of_min_cost_two_steps_entail_wit_2_1` failed first with `No such assumption`, then with a failed match for the preserved `prev1` equality.
- Trigger: after `pre_process; entailer!; try lia`, the remaining subgoals were not in the assertion text order; the first subgoal was the `cur` heap permission, followed by sum bound, nonnegativity, preserved bound, recurrence, and preserved semantic equality.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`, witnesses `proof_of_min_cost_two_steps_entail_wit_2_1` and `proof_of_min_cost_two_steps_entail_wit_2_2`.
- Fix action: inspected the exact `coqtop` proof state, reordered both branch proofs to match the generated subgoal order, solved the heap permission with `store_int_undef_store_int`, and selected invariant facts explicitly.
- Result: both loop-preservation witnesses advanced past heap and simple pure goals.

- Stage: `proof_manual`, DP recurrence rewrite
- Phenomenon: the recurrence bullet failed with stale hypothesis rewrites and brittle inline `sublist` rewrites.
- Trigger: the script attempted to rewrite with a hypothesis name that referred to `0 <= prev2`, and tried to perform all `sublist 0 (i + 1)` decomposition directly inside the witness.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`, recurrence bullets in both loop-preservation witnesses.
- Fix action: added helper lemma `min_cost_two_steps_z_prefix_snoc`, proving the prefix DP snoc recurrence from `sublist_split`, `sublist_single`, `min_cost_two_steps_z_snoc`, and `sublist_sublist00`; rewrote the branch recurrence bullets to call this helper and then use `Z.min_l` / `Z.min_r`.
- Result: both loop-preservation witnesses compiled.

- Stage: `proof_manual`, return witness
- Phenomenon: `proof_of_min_cost_two_steps_return_wit_2` failed with setoid-rewrite unresolved evars at `rewrite H12 in H4`.
- Trigger: rewriting the length equality inside the semantic invariant invoked setoid rewriting in a context where a plain goal-side rewrite was sufficient.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`, return witness.
- Fix action: after proving `i_2 = n_pre`, rewrote the goal using the semantic invariant and used `sublist_self` after rewriting `Zlength l = n_pre` on the goal side.
- Result: `proof_manual.v` compiled.

- Stage: `compile` and cleanup
- Phenomenon: final verification required compiling all generated Coq files and removing non-`.v` artifacts.
- Trigger: completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, no `Admitted.` / new `Axiom` in manual proof, and no non-`.v` intermediates under `coq/`.
- Location: `output/verify_20260420_222721_min_cost_two_steps/coq/generated/`.
- Fix action: compiled `original/min_cost_two_steps.v`, `min_cost_two_steps_goal.v`, `min_cost_two_steps_proof_auto.v`, `min_cost_two_steps_proof_manual.v`, and `min_cost_two_steps_goal_check.v` with the full template from `doc/experiences/COMPILE.md`; checked `proof_manual.v` for `Admitted.` / `Axiom`; deleted non-`.v` files under `coq/`.
- Result: verification succeeded and `coq/` contains only generated `.v` files.
