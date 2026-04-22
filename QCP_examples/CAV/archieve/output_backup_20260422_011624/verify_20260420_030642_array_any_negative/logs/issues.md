# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: no

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was freshly bootstrapped and still contained the script placeholders.
- Localization: `logs/workspace_fingerprint.json`
- Fix: read the controlled vocabulary from `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/retrieval/INDEX.md`, then filled in a concrete semantic description and controlled keywords for an array search with a for-loop, early branch, loop invariant, and preserved heap.
- Result: the fingerprint now has non-empty semantic content and uses only controlled keyword keys and values; after verification it also records `verification_status: goal_check_passed`.

## Annotation Layer

- Phenomenon: the active annotated copy had no invariant for the `for (i = 0; i < n; ++i)` scan loop.
- Trigger: the final `return 0` path needs a full-range universal fact `(forall i, 0 <= i < n => l[i] >= 0)`, but without a loop-head invariant the verifier has no durable summary of the already scanned prefix.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_030642_array_any_negative.c`
- Fix:
  - appended detailed reasoning to `logs/annotation_reasoning.md`;
  - added a loop invariant preserving `0 <= i && i <= n`, `a == a@pre`, `n == n@pre`, the prefix fact `(forall (j: Z), (0 <= j && j < i) => l[j] >= 0)`, and `IntArray::full(a, n, l)`;
  - added a loop-exit assertion immediately after the loop fixing `i == n` and restating the full-range nonnegative property before `return 0`.
- Result: the next clean `symexec` pass succeeded and generated fresh Coq artifacts.

## Symexec Invocation

- Phenomenon: probing `/home/yangfp/QualifiedCProgramming/linux-binary/symexec --help` produced `goal file not specified`; this binary does not expose a conventional help page and requires explicit output-file flags.
- Trigger: command-line discovery before the real symbolic execution pass.
- Localization: terminal output from the probe; the real run log is `logs/qcp_run.log`.
- Fix: used the canonical repository invocation shape with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--input-file`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260420_030642_array_any_negative`, and `--no-exec-info`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`, and `coq/generated/` contains the fresh goal, proof-auto, proof-manual, and goal-check files.

## Manual Proof

- Phenomenon: after successful symbolic execution, `coq/generated/array_any_negative_proof_manual.v` contained no generated theorem bodies and no `Admitted.` placeholders.
- Trigger: all generated obligations for this annotated program were discharged by generated axioms in the goal plus auto proof/check structure; no manual witness theorem was emitted in the manual file.
- Localization: `coq/generated/array_any_negative_proof_manual.v`
- Fix: no manual proof edit was required, so `logs/proof_reasoning.md` was intentionally not created.
- Result: `rg -n "Admitted\.|^Axiom\b" coq/generated/array_any_negative_proof_manual.v` returns no matches.

## Compile Replay

- Phenomenon: final verification required compiling all generated Coq files, including `goal_check.v`.
- Trigger: the verify workflow completion criteria require the current generated files to compile with the full load-path template.
- Localization: `logs/compile.log`
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the stable `BASE` load path and workspace-specific `-Q "$ORIG" ""` plus `-R "$GEN" SimpleC.EE.CAV.verify_20260420_030642_array_any_negative`; skipped `original/array_any_negative.v` because no optional input V was provided.
- Result: `array_any_negative_goal.v`, `array_any_negative_proof_auto.v`, `array_any_negative_proof_manual.v`, and `array_any_negative_goal_check.v` all compiled successfully.

## Cleanup

- Phenomenon: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` output.
- Localization: `coq/generated/`
- Fix: deleted all non-`.v` files under `coq/` after the successful compile replay.
- Result: only the four generated `.v` files remain under `coq/generated/`.
