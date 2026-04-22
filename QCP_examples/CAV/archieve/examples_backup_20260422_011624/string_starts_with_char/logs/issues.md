# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: no
- Manual proof required: yes

## Fingerprint Initialization

- Phenomenon: the initialized `logs/workspace_fingerprint.json` had empty `semantic_description` and `{}` keywords.
- Trigger: the workspace was bootstrapped before task-specific semantic classification.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled `semantic_description` and controlled-vocabulary keywords for a straight-line string/pointer selection function. After successful verification, added controlled `verification_status` values.
- Result: the fingerprint no longer contains empty semantic fields and all keyword keys/values come from the retrieval index vocabulary.

## Symexec

- Phenomenon: no symbolic execution blocker occurred.
- Trigger: ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` manually with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--input-file`, `--coq-logic-path`, `--no-exec-info`, and `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`.
- Localization: `logs/qcp_run.log`.
- Fix: no annotation repair was needed; the active annotated file already matched the input and the program has no loops.
- Result: `qcp_run.log` ended with `Successfully finished symbolic execution`, and fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files were generated.

## Manual Return Witnesses

- Phenomenon: generated `coq/generated/string_starts_with_char_proof_manual.v` contained three `Admitted.` return witnesses.
- Trigger: the postcondition is a three-way disjunction over empty string, first-character-equals, and first-character-differs cases; these branch facts were not discharged automatically.
- Localization:
  - `proof_of_string_starts_with_char_return_wit_1`
  - `proof_of_string_starts_with_char_return_wit_2`
  - `proof_of_string_starts_with_char_return_wit_3`
- Fix: used `CharArray.full_length` to recover `Zlength l = n`, destructed `l`, derived either `n = 0` or `0 < n`, simplified the first-character facts, selected the correct left-associated postcondition disjunct, and finished the unchanged heap frame with `entailer!`.
- Result: `string_starts_with_char_proof_manual.v` compiles and no longer contains `Admitted.`.

## Branch Selection Shape

- Phenomenon: the first proof compile failed with `Error: Not an inductive goal with 2 constructors.` at the initial attempt to use `right; right` for the empty-string branch.
- Trigger: the generated three-branch postcondition is left-associated as `((branch1 || branch2) || branch3)`.
- Localization: `coq/generated/string_starts_with_char_proof_manual.v`, `proof_of_string_starts_with_char_return_wit_1`.
- Fix: selected the third branch with `right`, the second with `left; right`, and the first with `left; left`.
- Result: branch selection advanced to the remaining pure/heap entailment.

## Entailment Timing

- Phenomenon: a later proof compile failed with `Error: Tactic failure: Cannot find witness.` after selecting the empty-string branch and running `entailer!`.
- Trigger: the proof derived `n = 0` after `entailer!`, but the selected pure branch required that fact during entailment.
- Localization: `coq/generated/string_starts_with_char_proof_manual.v`, `proof_of_string_starts_with_char_return_wit_1`.
- Fix: moved branch-specific facts before disjunct selection and completed the remaining pure conjunction using `simpl; repeat split; auto; lia`.
- Result: `proof_manual.v` compiled, and then `goal_check.v` compiled successfully.

## Final Compile And Cleanup

- Phenomenon: Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under `coq/generated/`.
- Trigger: standard `coqc` compilation of generated files.
- Localization: `output/verify_20260420_183012_string_starts_with_char/coq/generated/`.
- Fix: removed all non-`.v` files under the workspace `coq/` directory after successful compilation.
- Result: only `.v` generated Coq sources remain in `coq/`.
