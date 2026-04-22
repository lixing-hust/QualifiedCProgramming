# Issues

## Annotation And Symexec

- Phenomenon: the original active annotated file had no loop invariant for the `for` scan, so the final `return 0` path had no durable fact proving every array element differs from `x + y`.
- Trigger: `array_any_equal_sum` returns early on a matching element and otherwise needs a universal postcondition at loop exit.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_172537_array_any_equal_sum.c`, immediately before the `for` loop and immediately after loop exit.
- Fix: added a loop invariant carrying `0 <= i <= n`, unchanged parameters, `target == x + y`, target integer range, `IntArray::full(a, n, l)`, and the processed-prefix fact `(forall (j: Z), (0 <= j && j < i) => l[j] != target)`. Added a loop-exit assertion fixing `i == n` and restating the non-membership fact over `0 <= j < n`.
- Result: after clearing stale generated files, `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` completed successfully and regenerated `array_any_equal_sum_goal.v`, `array_any_equal_sum_proof_auto.v`, `array_any_equal_sum_proof_manual.v`, and `array_any_equal_sum_goal_check.v`.

## Manual Proof

- Phenomenon: no manual proof blocker remained after symbolic execution.
- Trigger: `coq/generated/array_any_equal_sum_proof_manual.v` contained imports only and no generated theorem bodies requiring manual proof.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_172537_array_any_equal_sum/coq/generated/array_any_equal_sum_proof_manual.v`.
- Fix: no manual proof edit was needed.
- Result: `array_any_equal_sum_proof_manual.v` compiled and contains no `Admitted.` proof body and no top-level `Axiom` declaration.

## Compile And Cleanup

- Phenomenon: the workflow requires a complete compile replay through `goal_check.v` and cleanup of Coq intermediate files before success can be recorded.
- Trigger: `coqc` generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` artifacts in `coq/generated/`.
- Localization: compile log `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_172537_array_any_equal_sum/logs/compile_full.log` and generated directory `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_172537_array_any_equal_sum/coq/generated/`.
- Fix: compiled `array_any_equal_sum_goal.v`, `array_any_equal_sum_proof_auto.v`, `array_any_equal_sum_proof_manual.v`, and `array_any_equal_sum_goal_check.v` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented load-path template. Removed all non-`.v` files under the workspace `coq/` directory afterward.
- Result: the full compile chain exited with status 0, `goal_check.v` compiled, and `find coq -type f ! -name '*.v'` returned no files.
