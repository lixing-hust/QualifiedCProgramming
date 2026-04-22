# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was bootstrapped before task-specific semantic classification.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045238_is_multiple/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled in a concrete description for a scalar modulo branch and selected only controlled vocabulary keys and values.
- Result: the fingerprint now has a non-empty semantic description and records `verification_status: goal_check_passed` after final compile.

## Annotation check

- Phenomenon: the active annotated copy had no extra `Inv` or `Assert` annotations beyond the original Require/Ensure.
- Trigger: `is_multiple` has no loop, heap predicate, or intermediate ownership transition; the function only branches on `a % b == 0`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_045238_is_multiple.c`.
- Fix action: did not add annotation reasoning or edit the annotated C because there was no concrete annotation failure and no invariant/assertion need.
- Result: the unchanged annotated copy was sufficient for symbolic execution.

## Symexec invocation

- Phenomenon: the workspace initially had no generated Coq VC files under `coq/generated/`.
- Trigger: verification had not yet run `symexec` for this active annotated file.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045238_is_multiple/logs/qcp_run.log`.
- Fix action: created `coq/generated/`, cleared stale generated targets if present, and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--goal-check-file`, `--input-file`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_045238_is_multiple`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, and `--no-exec-info`.
- Result: `symexec_status: 0`; fresh `is_multiple_goal.v`, `is_multiple_proof_auto.v`, `is_multiple_proof_manual.v`, and `is_multiple_goal_check.v` were generated.

## Manual proof obligations

- Phenomenon: `is_multiple_proof_manual.v` contained imports only and no generated lemma/theorem bodies.
- Trigger: the straight-line branch proof obligations were discharged by generated/common proof infrastructure, with no manual witness required in the manual file.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045238_is_multiple/coq/generated/is_multiple_proof_manual.v`.
- Fix action: skipped `logs/proof_reasoning.md` and manual proof edits because there was no manual theorem to prove.
- Result: `is_multiple_proof_manual.v` contains no `Admitted.` and no local `Axiom` declaration.

## Compile replay and cleanup

- Phenomenon: final verification required replaying Coq compilation with the workspace-specific load path.
- Trigger: the workflow requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile before marking success.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045238_is_multiple/logs/compile.log`.
- Fix action: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260421_045238_is_multiple`, then deleted all non-`.v` files under `coq/`.
- Result: compile replay ended with `compile_status: 0`; after cleanup, `coq/` contains only `.v` files.
