# Issues

## 2026-04-21T05:37:00+08:00 - Repository-level docs, workspace-local edits

- Phenomenon: the current workspace initially contained only `logs/` and `original/min_of_three.c`, so `doc/retrieval/INDEX.md` was not present under the workspace path.
- Trigger: attempted to read `doc/retrieval/INDEX.md` with the workspace as the current directory.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_053416_min_of_three`; repository-level docs live under `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/`.
- Fix action: read the workflow documents from the repository-level `doc/` tree, but kept writable task artifacts limited to the fixed workspace and the active annotated file path.
- Result: `logs/workspace_fingerprint.json` was updated early with a non-empty semantic description and controlled-vocabulary keywords.

## 2026-04-21T05:37:00+08:00 - No annotation changes needed

- Phenomenon: `min_of_three` has no loops, heap predicates, or array/string shape obligations; the active annotated C file already matched the input contract.
- Trigger: inspected `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/min_of_three.c` and `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_053416_min_of_three.c` before symbolic execution.
- Location: the two sequential `if` statements that update scalar local `m`.
- Fix action: did not add `Inv`, `Assert`, or bridge assertions, so `logs/annotation_reasoning.md` was intentionally not created.
- Result: `symexec` completed successfully on the unmodified active annotated C file.

## 2026-04-21T05:37:00+08:00 - Verification and compile replay

- Phenomenon: symbolic execution generated `min_of_three_goal.v`, `min_of_three_proof_auto.v`, `min_of_three_proof_manual.v`, and `min_of_three_goal_check.v`.
- Trigger: ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit generated output paths, `--goal-check-file`, `--input-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_053416_min_of_three.c`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_053416_min_of_three`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, and `--no-exec-info`.
- Location: generated files under `coq/generated/`.
- Fix action: no manual proof edit was needed because `min_of_three_proof_manual.v` contains no theorem obligations and no `Admitted.` or top-level `Axiom`. Then compiled `goal`, `proof_auto`, `proof_manual`, and `goal_check` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented load-path template.
- Result: all four generated Coq files compiled successfully; final cleanup deleted all non-`.v` Coq intermediates under `coq/`.
