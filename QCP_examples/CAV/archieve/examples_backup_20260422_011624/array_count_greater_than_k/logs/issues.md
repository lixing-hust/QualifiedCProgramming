# Verification Issues

## Empty Fingerprint Fields In Initialized Workspace

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and empty `keywords` object.
- Trigger: the workspace was initialized before this verify pass and still had placeholder fingerprint content.
- Location: `logs/workspace_fingerprint.json`, fields `semantic_description` and `keywords`.
- Fix: read `doc/retrieval/INDEX.md`, filled a concrete semantic description, and used only controlled vocabulary keys and values. After final verification, added `verification_status: goal_check_passed`.
- Result: the fingerprint now has non-empty semantics and controlled keywords.

## Missing Loop Invariant In Active Annotated Copy

- Phenomenon: the active annotated C initially matched the input and had no `Inv` before the `for` loop and no immediate post-loop assertion.
- Trigger: verifying a prefix-counting scan requires preserving the relationship between `cnt` and the already processed prefix; without an invariant, `symexec` would not have enough information to prove the loop step or return condition.
- Location: `annotated/verify_20260420_171225_array_count_greater_than_k.c`, before the loop and immediately after the loop.
- Fix: added an invariant carrying `0 <= i && i <= n`, unchanged parameter equalities `a == a@pre`, `n == n@pre`, `k == k@pre`, the prefix summary `cnt == array_count_greater_than_k_spec(sublist(0, i, l), k)`, and `IntArray::full(a, n, l)`. Added a loop-exit assertion fixing `i == n` and exposing the full-list count.
- Result: a clean `symexec` run completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual Proof Obligations After Symexec

- Phenomenon: `coq/generated/array_count_greater_than_k_proof_manual.v` contained five `Admitted.` obligations: `safety_wit_3`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `entail_wit_3`.
- Trigger: the generated VCs needed pure list/count facts for appending one processed element and a bound showing the count is between `0` and the processed prefix length.
- Location: `coq/generated/array_count_greater_than_k_proof_manual.v`.
- Fix: added local helper lemmas `array_count_greater_than_k_spec_app_single` and `array_count_greater_than_k_spec_bounds`; used the bounds lemma plus `store_int_range` to prove `cnt + 1` is in signed-int range, and used sublist splitting plus the append-singleton lemma to prove the two loop-preservation entailments.
- Result: `proof_manual.v` compiles and contains no `Admitted.` proof and no top-level `Axiom` declaration.

## Compile Replay And Cleanup

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` byproducts under `coq/generated/`.
- Trigger: normal `coqc` compilation of the generated files.
- Location: `output/verify_20260420_171225_array_count_greater_than_k/coq/generated/`.
- Fix: ran the full compile replay from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented load-path template, then deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `original/array_count_greater_than_k.v`, `array_count_greater_than_k_goal.v`, `array_count_greater_than_k_proof_auto.v`, `array_count_greater_than_k_proof_manual.v`, and `array_count_greater_than_k_goal_check.v` all compile; the cleanup check reports no non-`.v` files under `coq/`.
