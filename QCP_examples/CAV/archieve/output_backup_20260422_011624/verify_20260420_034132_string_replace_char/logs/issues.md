# Verify Issues

## Missing Loop Invariant

- Phenomenon: the active annotated C initially matched the input and had no invariant for the `while (1)` loop.
- Trigger: `string_replace_char` updates the string in place one character at a time, so the verifier needs a loop summary describing which prefix has already been transformed and which suffix is still original.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_034132_string_replace_char.c`, loop immediately after `int i = 0;`.
- Fix: added an invariant with `exists l1 l2`, bounds `0 <= i <= n`, parameter identities for `s`, `old_c`, and `new_c`, the split `l == app(l1, l2)`, length facts, the original nonzero-character fact, and heap shape `CharArray::full(s, n + 1, app(app(string_replace_char_spec(l1, old_c, new_c), l2), cons(0, nil)))`.
- Result: rerunning `symexec` generated fresh `string_replace_char_goal.v`, `string_replace_char_proof_auto.v`, `string_replace_char_proof_manual.v`, and `string_replace_char_goal_check.v`.

## Manual Proof Obligations

- Phenomenon: after successful symbolic execution, `string_replace_char_proof_manual.v` contained four `Admitted.` obligations: `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.
- Trigger: the remaining goals are list/heap entailments for initialization, loop-step prefix extension in the replacement branch, loop-step prefix extension in the nonreplacement branch, and loop exit.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_034132_string_replace_char/coq/generated/string_replace_char_proof_manual.v`.
- Fix: added local helper lemmas for `string_replace_char_spec` over append, length preservation, `replace_char` equality/disequality cases, current-head recovery after the transformed prefix, replacement-branch list rewriting, and nonreplacement branch preservation. Then used these helpers to complete all four generated witnesses.
- Result: `string_replace_char_proof_manual.v` compiles and contains no `Admitted.` proof and no top-level `Axiom` declaration.

## Proof Script Compatibility Iterations

- Phenomenon: the first manual compile failed in helper lemma `string_replace_char_spec_zlength` with `Tactic failure: Cannot find witness`.
- Trigger: the proof used `rewrite !Zlength_cons; lia`, but this Coq environment did not robustly use the induction hypothesis through arithmetic automation.
- Fix: rewrote the helper proof to explicitly rewrite by the induction hypothesis and finish by `reflexivity`.
- Result: compilation advanced to the generated witnesses.

- Phenomenon: the next compile failed in `proof_of_string_replace_char_entail_wit_1` with `Error: No such goal.`
- Trigger: `entailer!` already solved the initialization witness after choosing `l1 = nil` and `l2 = l`; copied cleanup lines then ran after the goal was closed.
- Fix: removed the dead `Zlength_correct` and `Zlength_app_cons` cleanup.
- Result: compilation advanced to the loop-step witness.

- Phenomenon: `proof_of_string_replace_char_entail_wit_2_1` first failed with `Found no subterm matching "?M ++ nil" in H2`.
- Trigger: generated hypothesis numbering differed from the closest copied example because this witness has an extra leading pure fact. `H2` was a bound, not the list split.
- Fix: adjusted the script to use the current generated hypotheses: `H4` for the list split, `H6` for `Zlength l1_2 = i`, and `H7` for `Zlength l2_2 = n - i`, with corresponding fixes in the other loop-step and return witnesses.
- Result: compilation advanced past the hypothesis-numbering issue.

- Phenomenon: the nil-suffix branch then failed at `app_Znth2` with `Found no subterm matching "Zlength (string_replace_char_spec ...)" in the current goal`.
- Trigger: the branch expression still contained an `++ nil` layer, so the append shape was not normalized before applying `app_Znth2`.
- Fix: rewrote `app_nil_r` in the branch facts first and derived the contradiction directly from the `Znth ... <> 0` fact.
- Result: full compile replay succeeded for original spec, goal, proof_auto, proof_manual, and goal_check.

## Final Outcome

- `symexec` succeeded on the latest annotated file.
- `string_replace_char_goal.v`, `string_replace_char_proof_auto.v`, `string_replace_char_proof_manual.v`, and `string_replace_char_goal_check.v` all compiled successfully with the workspace load path.
- `string_replace_char_proof_manual.v` contains no `Admitted.` proof and no top-level `Axiom` declaration.
- Non-`.v` Coq intermediate files under the workspace `coq/` directory were removed after the successful compile pass.
