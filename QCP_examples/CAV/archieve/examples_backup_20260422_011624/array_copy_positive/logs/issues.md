# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was freshly initialized with placeholder metadata.
- Localization: `logs/workspace_fingerprint.json`
- Fix: read `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/retrieval/INDEX.md`, then filled a concrete semantic description and controlled keywords for a for-loop array transform that preserves the input array and writes selected values to the output array.
- Result: the fingerprint now has non-empty semantic content, uses only controlled vocabulary keys and values, and records `verification_status` as `goal_check_passed` and `proof_check_passed`.

## Annotation Layer

- Phenomenon: the active annotated C file had no invariant for `for (i = 0; i < n; ++i)`.
- Trigger: the postcondition needs an existential result list `lr` whose elements satisfy a positive/nonpositive case split over `la`, but without a loop-head invariant the verifier has no durable description of the processed output prefix.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_173024_array_copy_positive.c`
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md` and added a prefix/suffix invariant with `out` modeled as `app(l1, l2)`, where `l1` has length `i` and satisfies the output rule, while `l2` has length `n@pre - i` and equals the untouched suffix of `lo`. The invariant also preserves `a == a@pre`, `out == out@pre`, `n == n@pre`, and the length facts for `la` and `lo`.
- Result: the invariant supplied the loop semantics needed for symbolic execution and final return proof.

## Parser Syntax

- Phenomenon: the first clean `symexec` run failed before VC generation with `bison: syntax error, unexpected PT_COMMA, expecting PT_REQUIRE`.
- Trigger: the active annotated copy inherited `With la, lo`, but this frontend accepts space-separated binders.
- Localization: `logs/qcp_run.log`, `annotated/verify_20260420_173024_array_copy_positive.c:6:12`
- Fix: changed only the active annotated copy from `With la, lo` to `With la lo`; the `Require` and `Ensure` formulas were unchanged.
- Result: the next clean `symexec` run parsed the program and completed successfully.

## Symexec

- Phenomenon: symbolic execution needed to be rerun after each annotation edit.
- Trigger: the invariant insertion and binder syntax fix changed the annotated verification input.
- Localization: `logs/qcp_run.log`
- Fix: created `coq/generated/`, cleared stale generated targets, and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit goal, proof-auto, proof-manual, proof-check, input, strategy path, and logic path flags for `SimpleC.EE.CAV.verify_20260420_173024_array_copy_positive`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`, and fresh `array_copy_positive_goal.v`, `array_copy_positive_proof_auto.v`, `array_copy_positive_proof_manual.v`, and `array_copy_positive_goal_check.v` were generated.

## Manual Proof

- Phenomenon: `coq/generated/array_copy_positive_proof_manual.v` initially contained four `Admitted.` obligations: `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.
- Trigger: the generated VCs required explicit list witnesses for initializing the loop invariant, extending the processed prefix in each branch, and instantiating the final result list at loop exit.
- Localization: `coq/generated/array_copy_positive_proof_manual.v`
- Fix: added a local `list_eq_by_Znth` helper and completed all four witness lemmas. The branch proofs reconstruct the untouched suffix as `sublist i n_pre lo`, rewrite the `replace_Znth` result into an extended prefix plus advanced suffix, and discharge the positive/nonpositive case split. The return proof derives `i_2 = n_pre`, proves the suffix is `nil`, and uses `l1` as the final `lr`.
- Result: `array_copy_positive_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Proof Script Iterations

- Phenomenon: the first manual compile failed at line 126 because the script applied `H6` as the prefix semantic hypothesis, but in this generated proof state `H6` was `Zlength l2_2 = n_pre - i`.
- Trigger: the initial proof reused a fragile generated hypothesis name from a similar example.
- Localization: `logs/compile.log`, `coq/generated/array_copy_positive_proof_manual.v`
- Fix: replaced brittle hypothesis-name references with `match goal` clauses that select the processed-prefix universal hypothesis by type.
- Result: the branch proofs advanced to later side conditions.

- Phenomenon: the next compile failed at line 134 with `Found no subterm matching "Zlength (?M ++ ?M)" in the current goal`.
- Trigger: the proof tried to rewrite `Zlength_app` in a side condition that Coq had already simplified.
- Localization: `logs/compile.log`, `coq/generated/array_copy_positive_proof_manual.v`
- Fix: replaced the overly specific rewrite sequence with plain `lia` for those side conditions.
- Result: both branch witnesses compiled.

- Phenomenon: the following compile failed in `return_wit_1` because `H5` was a suffix length equality, not the processed-prefix semantic fact needed for the postcondition.
- Trigger: another brittle generated hypothesis-name reference.
- Localization: `logs/compile.log`, `coq/generated/array_copy_positive_proof_manual.v`
- Fix: selected the return proof's prefix universal hypothesis by type and applied it to the postcondition index.
- Result: `proof_manual.v` compiled successfully.

## Compile Replay

- Phenomenon: final verification required the complete ordered Coq compile chain through `goal_check.v`.
- Trigger: verify completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile with the workspace load path.
- Localization: `logs/compile.log`
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260420_173024_array_copy_positive`. No optional original `.v` existed, so that compile step was skipped.
- Result: the final compile replay compiled `goal`, `proof_auto`, `proof_manual`, and `goal_check` successfully.

## Cleanup

- Phenomenon: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260420_173024_array_copy_positive/coq/generated/`
- Fix: deleted all non-`.v` files under `coq/` after successful compilation.
- Result: `find coq -type f ! -name '*.v'` returns no files.
