# Issues

## Fingerprint initialization

- Phenomenon: the initialized `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` keywords.
- Trigger: workspace bootstrap left task-specific semantic classification blank.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and controlled-vocabulary keywords for in-place selection sort over an integer array.
- Result: the fingerprint now has non-empty semantic fields and controlled keyword keys/values. After the final compile attempt, `verification_status` was updated to include `goal_check_passed`, `manual_witness_needed`, and `auto_proof_contains_admitted`.

## Symexec option syntax

- Phenomenon: the first manual `symexec` run exited immediately with `goal file not specified` and `Start to symbolic execution on program : (null)`.
- Trigger: the binary expects long options in `--name=value` form, but the first invocation used separated `--name value` arguments.
- Localization: `logs/qcp_run.log`.
- Fix: reran `symexec` with `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, and `--input-file=...`.
- Result: symbolic execution ran on `annotated/verify_20260421_173306_selection_sort.c`.

## Generated Coq absolute import

- Phenomenon: the first successful `symexec` generated Coq files containing `From /home/yangfp/QualifiedCProgramming/QCP_examples/ Require Import selection_sort_goal.`, and `coqc` failed with `Syntax error: [global] expected after 'From'`.
- Trigger: `--coq-logic-path` was passed as an absolute filesystem path.
- Localization: `coq/generated/selection_sort_proof_auto.v`, line 12 in that generation.
- Fix: cleared generated files and reran `symexec` with `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_173306_selection_sort`.
- Result: generated imports became valid, e.g. `From SimpleC.EE.CAV.verify_20260421_173306_selection_sort Require Import selection_sort_goal.`, and the full compile template ran successfully.

## Manual witness blocker

- Phenomenon: `coq/generated/selection_sort_proof_manual.v` still contains `Proof. Admitted.` for `proof_of_selection_sort_entail_wit_4`.
- Trigger: the outer-loop preservation proof after the final swap requires proving that a non-adjacent swap preserves permutation, extends the sorted prefix, and preserves prefix-to-suffix ordering.
- Localization: `coq/generated/selection_sort_proof_manual.v`, theorem `proof_of_selection_sort_entail_wit_4`.
- Fix attempted: completed `proof_of_selection_sort_entail_wit_1`, `proof_of_selection_sort_entail_wit_2`, and `proof_of_selection_sort_return_wit_1`; inspected the stable `entail_wit_4` proof state after choosing the swapped list and running `entailer!`.
- Result: `goal_check.v` compiles only because the remaining manual theorem is still admitted. Verification is therefore not successful under the workflow completion criteria.

## Manual witness blocker resolved in retry

- Phenomenon: retry compilation initially failed inside `proof_of_selection_sort_entail_wit_4` after replacing the `Admitted.` with a direct proof, with errors around chained range syntax, list-literal parsing under `sets` scope, brittle pointwise equality for the non-adjacent swap, and the generated order of remaining pure goals after `entailer!`.
- Trigger: the proof needed to bridge the concrete double `replace_Znth` expression from the two swap assignments with a semantic two-index swap over `l_inner`; Coq also parsed some convenient notations differently in this proof environment.
- Localization: `coq/generated/selection_sort_proof_manual.v`, helper lemmas for `selection_sort_swap` and theorem `proof_of_selection_sort_entail_wit_4`.
- Fix: replaced chained `0 <= i <= min_idx < ...` preconditions with explicit conjunctions; replaced list notations like `[x]` with `x :: nil`; proved a structural split lemma showing that swapping positions `Zlength pref` and `Zlength pref + 1 + Zlength mid` transforms `pref ++ x :: mid ++ y :: tail` into `pref ++ y :: mid ++ x :: tail`; reordered the theorem bullets to match the remaining goals after `entailer!`; added explicit length bridges from `IntArray.full_length` through `replace_Znth` length preservation.
- Result: `proof_of_selection_sort_entail_wit_4` is fully proved. The full compile template, including `selection_sort_goal_check.v`, succeeds without any `Admitted.` in `selection_sort_proof_manual.v`.

## Final compile and cleanup

- Phenomenon: Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under the workspace `coq/` tree.
- Trigger: standard `coqc` compilation of `original/selection_sort.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.
- Localization: `output/verify_20260421_173306_selection_sort/coq/`.
- Fix: removed all non-`.v` files under the workspace `coq/` tree after the compile check.
- Result: only generated `.v` sources remain under `coq/generated/`.

## Retry final compile and cleanup

- Phenomenon: the successful retry compile regenerated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under `output/verify_20260421_173306_selection_sort/coq/generated/`.
- Trigger: compiling `selection_sort_goal.v`, `selection_sort_proof_auto.v`, `selection_sort_proof_manual.v`, and `selection_sort_goal_check.v` with `coqc`.
- Localization: `output/verify_20260421_173306_selection_sort/coq/generated/`.
- Fix: removed all non-`.v` files under the workspace `coq/` tree after the successful compile.
- Result: cleanup check found no remaining non-`.v` files under `output/verify_20260421_173306_selection_sort/coq/`.
