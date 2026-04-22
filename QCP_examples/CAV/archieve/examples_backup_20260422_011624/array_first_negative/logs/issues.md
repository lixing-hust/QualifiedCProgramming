# Verify Issues

## Issue 1: First symexec wrapper used the wrong working directory

- Phenomenon: the first attempted `symexec` wrapper exited before invoking QCP because `output/verify_20260420_115922_array_first_negative/logs/qcp_run.log` could not be opened.
- Trigger: the command was launched from `/home/yangfp/QualifiedCProgramming` while using paths relative to `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV`.
- Location: command wrapper before the successful `symexec` run; no generated files were produced by this failed attempt.
- Fix: reran from `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV` with the active annotated file `annotated/verify_20260420_115922_array_first_negative.c` and workspace-relative output paths.
- Result: `symexec` completed with exit code `0` and generated `array_first_negative_goal.v`, `array_first_negative_proof_auto.v`, `array_first_negative_proof_manual.v`, and `array_first_negative_goal_check.v`.

## Issue 2: Initial annotated file lacked loop facts needed for first-negative semantics

- Phenomenon: the original active annotated file had no loop invariant, so symbolic execution would not preserve the fact that all indices before the current scan index are nonnegative.
- Trigger: the `for (i = 0; i < n; ++i)` loop scans an array and can return early; the postcondition needs either an early negative index with a nonnegative prefix or a final `-1` result with all elements nonnegative.
- Location: `annotated/verify_20260420_115922_array_first_negative.c`, before the loop and after the loop.
- Fix: added an invariant carrying `0 <= i && i <= n`, unchanged `a` and `n`, `IntArray::full(a, n, l)`, and `(forall (j: Z), (0 <= j && j < i) => l[j] >= 0)`. Added a loop-exit `Assert` fixing `i == n` and restating the full-range nonnegativity before `return -1`.
- Result: `symexec` succeeded and the generated `goal_check.v` compiled successfully.

## Issue 3: Generated Coq compilation artifacts needed cleanup

- Phenomenon: compiling generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` compilation of `goal`, `proof_auto`, `proof_manual`, and `goal_check`.
- Location: `output/verify_20260420_115922_array_first_negative/coq/generated/`.
- Fix: deleted all non-`.v` files under the current workspace `coq/` tree after successful compilation.
- Result: `find output/verify_20260420_115922_array_first_negative/coq -type f ! -name '*.v'` returned no files.
