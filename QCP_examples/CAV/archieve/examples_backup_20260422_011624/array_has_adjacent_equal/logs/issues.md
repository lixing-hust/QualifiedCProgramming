# Verify Issues

## Issue 1: Initial annotated file had no loop summary for adjacent-pair scan

- Phenomenon: the active annotated C copy was identical to the input and had no invariant for the `for (i = 1; i < n; ++i)` scan.
- Trigger: the postcondition needs either an early existential adjacent equal pair or, on the final `return 0` path, a universal fact that every adjacent pair index `1 <= i < n` is unequal.
- Location: `annotated/verify_20260420_121132_array_has_adjacent_equal.c`, before the loop.
- Fix: added a loop invariant carrying `1 <= i && i <= n + 1`, unchanged `a` and `n`, `IntArray::full(a, n, l)`, and the processed-prefix property `(forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1])`.
- Result: the invariant was strong enough for both the early-return branch and the final return witness after a clean `symexec` rerun.

## Issue 2: Loop-exit assertion interfered with local variable cleanup

- Phenomenon: the first `symexec` run after adding annotations failed with `Fail to Remove Memory Permission of i` at the final `return 0`.
- Trigger: a loop-exit `Assert` was placed immediately after the `for` loop and before `return 0`.
- Location: `logs/qcp_run.log` from the failed run, and `annotated/verify_20260420_121132_array_has_adjacent_equal.c` at the final return path.
- Fix: removed the post-loop `Assert` and relied on the loop invariant plus generated loop-exit condition `i_3 >= n_pre`.
- Result: the next clean `symexec` run exited with code `0`, and `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## Issue 3: Manual proof needed explicit model-level splitting

- Phenomenon: the generated `array_has_adjacent_equal_proof_manual.v` contained one admitted obligation, `proof_of_array_has_adjacent_equal_return_wit_2`.
- Trigger: this final return witness has to turn the invariant universal over `j < i_3` into the postcondition universal over `j < n_pre`, using the loop-exit fact `i_3 >= n_pre`.
- Location: `output/verify_20260420_121132_array_has_adjacent_equal/coq/generated/array_has_adjacent_equal_proof_manual.v`.
- Fix: replaced `Admitted.` with an unfolded proof that selects the left postcondition disjunct, uses `entailer!`, explicitly splits the model-level conjunction, and proves the universal by applying the invariant with `lia`.
- Result: `array_has_adjacent_equal_proof_manual.v` compiled successfully and contains no `Admitted.` or newly added `Axiom`.

## Issue 4: First proof attempt used the wrong post-automation goal shape

- Phenomenon: `compile_proof_manual.log` first reported `No product even after head-reduction` at `intros i [? ?]`, then after trimming too far reported `Attempt to save an incomplete proof`.
- Trigger: after `entailer!`, the remaining goal was not a Coq product but a model-level assertion conjunction `([|0 = 0|] && ([|forall i, ...|] && IntArray.full ...)) m`.
- Location: `logs/compile_proof_manual.log` and the `coqtop` probe recorded in `logs/proof_reasoning.md`.
- Fix: changed the proof to split that assertion-level conjunction explicitly before introducing the quantified index.
- Result: the full compile chain reached and compiled `array_has_adjacent_equal_goal_check.v`.

## Issue 5: Generated Coq compilation artifacts needed cleanup

- Phenomenon: successful `coqc` runs produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal Coq compilation of `goal`, `proof_auto`, `proof_manual`, and `goal_check`.
- Location: `output/verify_20260420_121132_array_has_adjacent_equal/coq/generated/`.
- Fix: deleted all non-`.v` files under the current workspace `coq/` tree after successful compilation.
- Result: `find output/verify_20260420_121132_array_has_adjacent_equal/coq -type f ! -name '*.v'` returned no files.
