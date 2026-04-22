# Verification Issues

## Missing Loop Invariant In Initial Annotated Copy

- Phenomenon: the active annotated file initially matched the input C exactly and had no `Inv` before the `for` loop and no post-loop assertion before `return 1`.
- Trigger: verifying `array_all_zero` requires the normal-exit path to prove `forall i, 0 <= i && i < n => l[i] == 0`, but without a loop invariant the verifier has no retained fact about the already-scanned prefix.
- Location: `annotated/verify_20260420_031341_array_all_zero.c`, before the loop at line 28 and after the loop at line 34 in the final file.
- Fix: added a prefix invariant stating `0 <= i <= n`, `a == a@pre`, `n == n@pre`, `(forall j, 0 <= j && j < i => l[j] == 0)`, and `IntArray::full(a, n, l)`. Added a loop-exit assertion fixing `i == n` and rewriting the prefix fact to the full range.
- Result: rerunning `symexec` succeeded; `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## First Symexec Attempt Used Wrong Relative Workspace Path

- Phenomenon: the first manual `symexec` shell command exited before invoking the verifier, with `/bin/bash` reporting that `output/verify_20260420_031341_array_all_zero/logs/qcp_run.log` and `logs/symexec_status.log` did not exist.
- Trigger: the command was run from `/home/yangfp/QualifiedCProgramming` while using paths relative to `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV`.
- Location: shell command path setup before `symexec`; no generated verifier output was produced by this failed attempt.
- Fix: reran `symexec` using absolute paths for the workspace outputs and the active annotated C file.
- Result: the corrected command generated `array_all_zero_goal.v`, `array_all_zero_proof_auto.v`, `array_all_zero_proof_manual.v`, and `array_all_zero_goal_check.v` in the current workspace.

## First Coq Compile Replay Used Wrong Working Directory

- Phenomenon: the first compile replay failed on `array_all_zero_goal.v` with `Cannot find a physical path bound to logical path int_auto with prefix AUXLib`.
- Trigger: the compile command was run from `/home/yangfp/QualifiedCProgramming` while using the `_CoqProject` paths that are relative to `/home/yangfp/QualifiedCProgramming/SeparationLogic`.
- Location: `logs/compile.log` from the failed replay showed missing paths such as `unifysl`, `auxlibs`, `StrategyLib`, and `Common`.
- Fix: reran the same ordered compile from `/home/yangfp/QualifiedCProgramming/SeparationLogic`, with `-R "$GEN" SimpleC.EE.CAV.verify_20260420_031341_array_all_zero` for the generated files and `-Q "$ORIG" ""` for the workspace original directory.
- Result: `array_all_zero_goal.v`, `array_all_zero_proof_auto.v`, `array_all_zero_proof_manual.v`, and `array_all_zero_goal_check.v` all compiled successfully.

## Cleanup

- Phenomenon: successful `coqc` replay produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Trigger: normal Coq compilation byproducts.
- Location: `output/verify_20260420_031341_array_all_zero/coq/generated/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory after successful compile replay.
- Result: `find output/verify_20260420_031341_array_all_zero/coq -type f ! -name '*.v'` returns no files.
