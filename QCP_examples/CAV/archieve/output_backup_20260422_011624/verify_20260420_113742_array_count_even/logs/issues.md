# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workspace was bootstrapped before task-specific semantic classification.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md`, then filled in a concrete semantic description and controlled keywords for an array-counting for-loop over a preserved input array.
- Result: the fingerprint now has non-empty semantic content and only uses controlled vocabulary keys and values; after final compile it also records `verification_status: goal_check_passed`.

## Missing loop invariant

- Phenomenon: the active annotated copy initially had no invariant for the `for (i = 0; i < n; ++i)` scan loop.
- Trigger: the postcondition requires `__return == array_count_even_spec(l)`, but without a loop-head invariant the verifier has no durable relation between `cnt` and the processed prefix of `l`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_113742_array_count_even.c`
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md`; added a loop invariant preserving `0 <= i && i <= n`, `a == a@pre`, `n == n@pre`, `cnt == array_count_even_spec(sublist(0, i, l))`, and `IntArray::full(a, n, l)`; added a loop-exit assertion fixing `i == n` and `cnt == array_count_even_spec(l)`.
- Result: the next clean `symexec` pass succeeded and generated fresh Coq artifacts.

## Symexec invocation

- Phenomenon: after annotation changes, generated VC files had to be regenerated from the current annotated source.
- Trigger: the verify workflow requires rerunning `symexec` after every `Inv` or `Assert` edit.
- Localization: `logs/qcp_run.log`
- Fix: cleared this workspace's old generated files and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit goal, proof-auto, proof-manual, goal-check, input-file, strategy path, Coq logic path, and `--no-exec-info` flags.
- Result: `qcp_run.log` ends with `Successfully finished symbolic execution`, and `coq/generated/` contains fresh `array_count_even_goal.v`, `array_count_even_proof_auto.v`, `array_count_even_proof_manual.v`, and `array_count_even_goal_check.v`.

## Manual proof obligations

- Phenomenon: the generated `array_count_even_proof_manual.v` contained five `Admitted.` placeholders:
  - `proof_of_array_count_even_safety_wit_6`
  - `proof_of_array_count_even_entail_wit_1`
  - `proof_of_array_count_even_entail_wit_2_1`
  - `proof_of_array_count_even_entail_wit_2_2`
  - `proof_of_array_count_even_entail_wit_3`
- Trigger: the generated VC needed manual list/spec facts for prefix extension and an integer range bound for `cnt + 1`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_113742_array_count_even/coq/generated/array_count_even_proof_manual.v`
- Fix: added local helper lemmas `array_count_even_spec_app_single` and `array_count_even_spec_bounds`, then proved the five generated witness lemmas using the same prefix-count proof pattern as the completed zero-count examples.
- Result: `array_count_even_proof_manual.v` contains no `Admitted.` and no newly introduced `Axiom`.

## First compile attempt did not fail fast

- Phenomenon: the first compile replay log showed a real Coq failure in `array_count_even_proof_manual.v`, but the shell command exited successfully because later commands continued.
- Trigger: the compile shell block did not use `set -e`, so the failing `coqc` command did not stop the script.
- Localization: `logs/compile.log` from the first replay; the stable failure was `line 84, characters 2-5: Error: Tactic failure: Cannot find witness.`
- Fix: recorded the proof failure in `logs/proof_reasoning.md`, normalized the true-branch case split to `rewrite H; destruct (Z.eq_dec 0 0); lia`, and reran the compile chain with `set -e`.
- Result: the second compile replay stopped on errors if any occurred and completed successfully through `array_count_even_goal_check.v`.

## Compile replay and cleanup

- Phenomenon: final verification required compiling the optional spec file and all generated Coq files under the workspace-specific load path.
- Trigger: the verify workflow completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile with the full template.
- Localization: `logs/compile.log`
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the stable `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260420_113742_array_count_even`; then deleted non-`.v` files under `coq/`.
- Result: `original/array_count_even.v`, `array_count_even_goal.v`, `array_count_even_proof_auto.v`, `array_count_even_proof_manual.v`, and `array_count_even_goal_check.v` all compiled successfully; after cleanup only `.v` source files remain under `coq/`.
