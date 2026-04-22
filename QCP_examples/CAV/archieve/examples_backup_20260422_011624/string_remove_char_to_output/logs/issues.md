## 2026-04-20 verification issues

### Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: workspace was initialized by the verify runner before semantic classification.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, filled a non-empty semantic description, and used only controlled-vocabulary keys/values. After proof remained incomplete, updated `verification_status` to `manual_witness_needed`.
- Result: fingerprint is non-empty and controlled-vocabulary compliant.

### Missing loop invariant

- Phenomenon: the active annotated C initially had no invariant for the `while (1)` scan, so symexec would not have enough information to preserve the input string, the filtered output prefix, and `j`.
- Trigger: loop copies only characters not equal to `c`, so the output index is not equal to the input index.
- Location: `annotated/verify_20260420_190707_string_remove_char_to_output.c`, before the `while` loop.
- Fix action: added an invariant with `l = app(l1, l2)`, `Zlength(l1) = i`, `j = Zlength(string_remove_char_to_output_spec(l1, c))`, preserved source memory, and output memory as `app(spec(l1,c), d1)`.
- Result: symexec progressed into the final terminator write.

### Final terminator write bridge

- Phenomenon: first symexec attempt after adding the invariant failed with `Assign Exec fail` at `out[j] = 0`.
- Trigger: the post-loop assertion exposed the output suffix as opaque `d1`, so the write checker could not focus the writable cell at offset `j`.
- Location: `annotated/verify_20260420_190707_string_remove_char_to_output.c:62`; evidence in `logs/qcp_run.log` from the failed run.
- Fix action: changed the loop-exit assertion to split the output as `app(app(string_remove_char_to_output_spec(l,c), cons(x,nil)), t)` and added `0 <= j && j <= n`.
- Result: the next clean symexec run completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

### Manual proof iteration

- Phenomenon: generated `string_remove_char_to_output_proof_manual.v` contained five admitted manual witnesses.
- Trigger: filter semantics require list reasoning for initialization, keep/drop loop branches, exit reconstruction, and final `replace_Znth`.
- Location: `coq/generated/string_remove_char_to_output_proof_manual.v`.
- Fix action: added local helper lemmas for filter append, single-character keep/drop, filtered length bound, current head after prefix, and replace-at-prefix-end; completed `entail_wit_1`, `entail_wit_2_1`, and `entail_wit_2_2`; partially repaired `entail_wit_3`.
- Result: `proof_manual.v` no longer contains `Admitted.` or new `Axiom`, but it still does not compile.

### Current blocker

- Phenomenon: `coqc` fails on `proof_of_string_remove_char_to_output_entail_wit_3` with `Attempt to save an incomplete proof (there are remaining open goals)`.
- Trigger: the loop-exit witness has been reduced through `i = n`, `l2 = nil`, and output suffix splitting, but Coq still reports an incomplete proof at `Qed`. Temporary `Show`/`Show Existentials` probing printed `No more goals`, so the remaining issue appears to be an unfocused/shelved proof state produced by the current script structure or automation.
- Location: `coq/generated/string_remove_char_to_output_proof_manual.v`, theorem `proof_of_string_remove_char_to_output_entail_wit_3`; failing log `logs/compile_proof_manual.log`.
- Fix action: removed debug `Show` commands, left the best current non-admitted script, and cleaned non-`.v` Coq intermediates.
- Result: verification is not complete; `goal_check.v` has not been compiled successfully.

### Retry repair: loop-exit stack cell

- Phenomenon: retry compilation still failed in `proof_of_string_remove_char_to_output_entail_wit_3` with `Attempt to save an incomplete proof`, but `coqtop` showed the remaining focused goal was `&( "i") # Int |-> Zlength l1 |-- &( "i") # Int |-> n`.
- Trigger: the proof had established loop exit as `Hi_eq_n : Zlength l1 = n` after `l2 = nil`, but did not rewrite the stack cell before calling `entailer!`.
- Location: `coq/generated/string_remove_char_to_output_proof_manual.v`, theorem `proof_of_string_remove_char_to_output_entail_wit_3`.
- Fix action: added `rewrite Hi_eq_n` after substituting `l = l1` and before splitting the output suffix.
- Result: `entail_wit_3` compiled and the next blocker moved to the return witness.

### Retry repair: return witness append shape

- Phenomenon: `proof_of_string_remove_char_to_output_return_wit_1` failed first because the rewrite targeted `replace_Znth j 0 (spec ++ x :: t_2)`, but the generated heap contained `replace_Znth j 0 ((spec ++ x :: nil) ++ t_2)`. A direct helper application then failed because the helper concluded the flattened RHS while the generated postcondition kept the nested append.
- Trigger: generated assertions preserve `app(app(spec, cons(x,nil)), t)` rather than immediately simplifying it to `spec ++ x :: t`.
- Location: `coq/generated/string_remove_char_to_output_proof_manual.v`, theorem `proof_of_string_remove_char_to_output_return_wit_1`; failing log `logs/compile_proof_manual.log`.
- Fix action: changed the local replacement fact to the nested generated shape, normalized the antecedent with `rewrite <- app_assoc; simpl`, rewrote using `replace_at_prefix_end`, and reassociated the result back to `(spec ++ 0 :: nil) ++ t_2`.
- Result: `proof_manual.v` compiled successfully.

### Final compile and cleanup

- Phenomenon: the previous run ended before `goal_check.v`; after the retry repairs the full ordered compile was rerun.
- Trigger: completion requires `original`, `goal`, `proof_auto`, `proof_manual`, and `goal_check` to compile with the current workspace load path.
- Location: logs `compile_original.log`, `compile_goal.log`, `compile_proof_auto.log`, `compile_proof_manual.log`, and `compile_goal_check.log`.
- Fix action: compiled all five files successfully, confirmed `proof_manual.v` contains no `Admitted.`, no new `Axiom`, and no `Show`, then deleted non-`.v` intermediates under `coq/`.
- Result: verification completed successfully; `goal_check.v` compiled and no non-`.v` files remain under the workspace `coq/` directory.
