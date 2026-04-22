# Verification Issues

## Issue 1: fingerprint placeholder had to be backfilled

- Stage: `workspace setup`
- Symptom: `logs/workspace_fingerprint.json` still had an empty `semantic_description` and `{}` for `keywords`.
- Trigger: the initialized workspace had not yet recorded semantic retrieval metadata.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154005_array_is_strictly_increasing/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled `semantic_description` and controlled-vocabulary `keywords` for the array adjacent-pair scan.
- Result: the fingerprint now has non-empty semantic content and includes `verification_status: goal_check_passed` after final verification.

## Issue 2: the unannotated early-return loop needed a prefix invariant

- Stage: `annotation`
- Symptom: the active annotated C initially matched the raw input and had no loop invariant or assertions around the `for (i = 1; i < n; ++i)` loop.
- Trigger: `symexec` needs a loop-head summary for the processed adjacent pairs and a direct witness for the early `return 0` branch.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_154005_array_is_strictly_increasing.c`.
- Fix: added an invariant at the loop head preserving `1 <= i && i <= n + 1`, unchanged `a` and `n`, full array ownership, and the processed-prefix property `forall j, 1 <= j && j < i -> l[j - 1] < l[j]`. Added an early-return assertion exposing witness `i` for `l[i - 1] >= l[i]`, and a loop-exit assertion exposing the full universal property for the `return 1` path.
- Result: a clean `symexec` run completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 3: one manual loop-exit entailment remained

- Stage: `proof`
- Symptom: `array_is_strictly_increasing_proof_manual.v` contained one generated placeholder, `proof_of_array_is_strictly_increasing_entail_wit_4`, with `Admitted.`.
- Trigger: the generated witness required proving that the invariant's prefix property over indices `< i` implies the post-loop assertion over indices `< n_pre`, using the loop-exit fact `i >= n_pre`.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154005_array_is_strictly_increasing/coq/generated/array_is_strictly_increasing_proof_manual.v`.
- Fix: replaced the placeholder with a direct proof using `pre_process`, `Intros`, `entailer!`, then applying the invariant hypothesis to the arbitrary postcondition index and discharging the inequality with `lia`.
- Result: `proof_manual.v` compiles, contains no `Admitted.`, and has no new axiom declarations.

## Issue 4: final cleanup was required after successful Coq compilation

- Stage: `compile / cleanup`
- Symptom: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` compilation of generated files.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154005_array_is_strictly_increasing/coq/generated/`.
- Fix: deleted all non-`.v` files under the current workspace's `coq/` directory after the successful compile chain.
- Result: `coq/` now contains only `.v` source files.

## Final status

- `symexec`: succeeded; `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.
- `goal.v`: compiled successfully.
- `proof_auto.v`: compiled successfully.
- `proof_manual.v`: compiled successfully.
- `goal_check.v`: compiled successfully.
- Completion time: `2026-04-20 15:44:05 +0800`.
