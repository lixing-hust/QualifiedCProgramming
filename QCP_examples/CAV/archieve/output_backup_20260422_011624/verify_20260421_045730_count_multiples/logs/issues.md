# Verification Issues

## Fingerprint Completion

- Phenomenon: `logs/workspace_fingerprint.json` initially contained an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was initialized before task-specific semantic classification.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045730_count_multiples/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled in a concrete scalar counting-loop description and used only controlled vocabulary keys and values. After final verification, added controlled `verification_status` values.
- Result: the fingerprint is non-empty and uses only controlled vocabulary from the retrieval index.

## Missing Loop Invariant

- Phenomenon: the active annotated copy initially had no invariant for `for (i = 1; i <= n; ++i)`.
- Trigger: the postcondition requires `__return == count_multiples_spec(n@pre, k@pre)`, but without an invariant the verifier has no relation between `cnt` and the processed range `1..i-1`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_045730_count_multiples.c`.
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md`; added a loop invariant preserving `1 <= i && i <= n + 1`, unchanged `n` and `k`, integer bounds, `0 <= cnt && cnt <= i - 1`, and `cnt == count_multiples_spec(i - 1, k)`; added a loop-exit assertion fixing `i == n + 1` and `cnt == count_multiples_spec(n, k)`.
- Result: after clearing stale generated files, the next `symexec` pass succeeded and generated fresh Coq artifacts.

## Symexec Invocation

- Phenomenon: after annotation changes, generated VC files had to be regenerated from the active annotated source.
- Trigger: the verify workflow requires rerunning `symexec` after every `Inv` or `Assert` edit.
- Localization: `logs/qcp_run.log` and `logs/symexec_status.txt`.
- Fix: created `coq/generated/`, removed stale generated targets, and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--goal-check-file`, `--input-file`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_045730_count_multiples`, and `--no-exec-info`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`; `logs/symexec_status.txt` records status `0` and elapsed time `1` second.

## Manual Proof Obligations

- Phenomenon: the generated `count_multiples_proof_manual.v` contained three `Admitted.` placeholders:
  - `proof_of_count_multiples_entail_wit_1`
  - `proof_of_count_multiples_entail_wit_2_1`
  - `proof_of_count_multiples_entail_wit_2_2`
- Trigger: the invariant preservation VCs needed pure reasoning about `count_multiples_spec` over one additional candidate and a case split on the C remainder test.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045730_count_multiples/coq/generated/count_multiples_proof_manual.v`.
- Fix: added local helper lemmas for `count_multiples_spec 0`, the relation between `Z.to_nat i` and `S (Z.to_nat (i - 1))`, the last processed index, and the one-step divisible/non-divisible spec updates; replaced all three `Admitted.` proof bodies.
- Result: `count_multiples_proof_manual.v` compiles and `rg -n "Admitted\\.|^Axiom\\b"` returns no matches for the manual proof file.

## First Manual Compile Failure

- Phenomenon: the first compile replay stopped in `count_multiples_proof_manual.v` with `Error: No such goal.`
- Trigger: `proof_of_count_multiples_entail_wit_1` had `pre_process; entailer!`, but `pre_process` had already discharged the entire initialization witness.
- Localization: `logs/compile_proof_manual.log`, line 85 of the then-current manual proof file.
- Fix: recorded the failure in `logs/proof_reasoning.md`, trimmed `proof_of_count_multiples_entail_wit_1` to just `pre_process.`, and reran the compile chain with `set -e`.
- Result: the second compile replay passed through `count_multiples_goal_check.v`.

## Compile Replay And Cleanup

- Phenomenon: final verification required compiling the optional spec file and all generated Coq files under the workspace-specific logical path.
- Trigger: the verify workflow requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, and requires `proof_manual.v` to contain no `Admitted.` or new `Axiom`.
- Localization: compile logs under `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_045730_count_multiples/logs/`.
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260421_045730_count_multiples`; removed all non-`.v` files under the workspace `coq/` directory afterward.
- Result: `original/count_multiples.v`, `count_multiples_goal.v`, `count_multiples_proof_auto.v`, `count_multiples_proof_manual.v`, and `count_multiples_goal_check.v` all compiled successfully; `find coq -type f ! -name '*.v'` returns no files.

