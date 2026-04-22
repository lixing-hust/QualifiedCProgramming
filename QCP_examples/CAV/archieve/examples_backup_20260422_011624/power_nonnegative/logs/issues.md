# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workspace was bootstrapped before task-specific semantic classification.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled in a concrete semantic description and controlled keywords for scalar repeated-multiplication exponentiation.
- Result: the fingerprint now has non-empty semantic content, uses only controlled vocabulary keys and values, and records `verification_status: goal_check_passed`.

## Missing loop invariant

- Phenomenon: the active annotated copy initially had no invariant for `for (i = 0; i < exp; ++i)`.
- Trigger: the postcondition requires `__return == power_nonnegative_z(base@pre, exp@pre)`, but without a loop-head invariant the verifier has no persistent relationship between `ans`, the number of completed multiplications, and the mathematical power function.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_024109_power_nonnegative.c`.
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md`; added a loop invariant preserving `0 <= i && i <= exp`, `base == base@pre`, `exp == exp@pre`, `ans == power_nonnegative_z(base, i)`, and `emp`.
- Result: the invariant gave symbolic execution enough loop-head state to generate verification conditions.

## Symexec invocation

- Phenomenon: after adding the invariant, generated VC files had to be regenerated from the current annotated source.
- Trigger: the verify workflow requires rerunning `symexec` after every `Inv` edit.
- Localization: `logs/qcp_run.log`.
- Fix: created `coq/generated/`, cleared stale generated targets, and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, `--input-file=...`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_024109_power_nonnegative`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, and `--no-exec-info`.
- Result: `qcp_run.log` ends with `Successfully finished symbolic execution`, and fresh `power_nonnegative_goal.v`, `power_nonnegative_proof_auto.v`, `power_nonnegative_proof_manual.v`, and `power_nonnegative_goal_check.v` were generated.

## Manual proof obligations

- Phenomenon: fresh `power_nonnegative_proof_manual.v` contained three `Admitted.` placeholders: `proof_of_power_nonnegative_safety_wit_3`, `proof_of_power_nonnegative_entail_wit_1`, and `proof_of_power_nonnegative_entail_wit_2`.
- Trigger: the generated VCs needed a local fact connecting the recursive Coq definition to one loop multiplication step: `power_nonnegative_z base (i + 1) = power_nonnegative_z base i * base` for nonnegative `i`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/coq/generated/power_nonnegative_proof_manual.v`.
- Fix: added local helper lemma `power_nonnegative_z_succ`; proved the safety witness by instantiating the contract overflow guard at `i + 1`; proved the loop preservation witness by rewriting with the successor lemma; kept the initialization witness at the minimal `pre_process` proof.
- Result: `power_nonnegative_proof_manual.v` contains no `Admitted.` and no newly introduced `Axiom`.

## Helper lemma binder collision

- Phenomenon: the first compile attempt failed in `power_nonnegative_proof_manual.v` with `The term "exp" has type "(?A -> model -> Prop) -> model -> Prop" while it is expected to have type "Z".`
- Trigger: the local helper lemma used a binder named `exp` while `Local Open Scope sac` was active, colliding with the separation-logic `exp` notation/function.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/coq/generated/power_nonnegative_proof_manual.v:30`.
- Fix: renamed the helper lemma exponent binder from `exp` to `e`.
- Result: the helper lemma compiled, and proof checking advanced to the next witness.

## Over-proved initialization witness

- Phenomenon: the second compile attempt failed with `Error: No such goal.` in `proof_of_power_nonnegative_entail_wit_1`.
- Trigger: `pre_process` had already closed the initialization witness, so the following explicit `entailer!; unfold power_nonnegative_z; reflexivity` tried to run after all goals were solved.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_024109_power_nonnegative/coq/generated/power_nonnegative_proof_manual.v:54`.
- Fix: shortened `proof_of_power_nonnegative_entail_wit_1` to `unfold power_nonnegative_entail_wit_1; pre_process.`
- Result: the full compile replay passed through `power_nonnegative_goal_check.v`.

## Compile replay and cleanup

- Phenomenon: final verification required compiling the optional Coq spec and all generated Coq files under the workspace-specific load path.
- Trigger: the verify workflow completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile with the full template.
- Localization: `logs/compile.log`.
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the stable base load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260421_024109_power_nonnegative`; then deleted non-`.v` Coq intermediate files.
- Result: `original/power_nonnegative.v`, `power_nonnegative_goal.v`, `power_nonnegative_proof_auto.v`, `power_nonnegative_proof_manual.v`, and `power_nonnegative_goal_check.v` all compiled successfully; after cleanup, `coq/` contains only `.v` files.
