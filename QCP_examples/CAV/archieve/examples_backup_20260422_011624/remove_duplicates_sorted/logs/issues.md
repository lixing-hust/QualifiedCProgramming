# Verification Issues

## Issue 1: initial `symexec` command used unsupported separated long options

- Phenomenon: the first manual `symexec` invocation exited with `goal file not specified` and reported the program as `(null)`.
- Trigger: this `symexec` binary expects long options in `--flag=value` form for file paths; the first run used `--goal-file <path>` style.
- Localization: `logs/qcp_run.log`.
- Fix action: reran `symexec` with `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, `--goal-check-file=...`, and `--input-file=...`.
- Result: symbolic execution exited with status 0 and generated fresh `remove_duplicates_sorted_goal.v`, `remove_duplicates_sorted_proof_auto.v`, `remove_duplicates_sorted_proof_manual.v`, and `remove_duplicates_sorted_goal_check.v`.

## Issue 2: unannotated loop had no invariant for two-pointer compaction

- Phenomenon: the active annotated C initially matched the input C and had no `Inv` before `for (i = 1; i < n; ++i)`.
- Trigger: the function mutates a compacted prefix while leaving an unconstrained gap between `j` and `i`; without a loop-head heap summary, the verifier cannot derive either future reads or the final prefix postcondition.
- Localization: `annotated/verify_20260421_140942_remove_duplicates_sorted.c`, loop before line containing `for (i = 1; i < n; ++i)`.
- Fix action: added an invariant with existential current heap list `lc`, bounds for `i` and `j`, `j = Zlength(remove_duplicates_sorted_spec(sublist 0 i l))`, pointwise agreement of `lc[0..j)` with the duplicate-free processed prefix, untouched suffix agreement for `lc[i..n)`, and `IntArray::full(a, n, lc)`.
- Result: `symexec` successfully generated verification conditions.

## Issue 3: manual proof required local list/spec helper lemmas

- Phenomenon: `proof_manual.v` contained five generated manual obligations after successful symbolic execution.
- Trigger: the auto proof could not derive the recurrence of `remove_duplicates_sorted_spec` over `sublist 0 (i + 1) l`, nor the `replace_Znth` pointwise facts needed for the unequal branch.
- Localization: `coq/generated/remove_duplicates_sorted_proof_manual.v`, witnesses `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `return_wit_1`, and `return_wit_2`.
- Fix action: added local helper lemmas for list equality by `Znth`, `replace_Znth` length/index behavior, the duplicate-removal snoc recurrence, singleton prefix initialization, and full-prefix sublist equality; then replaced all manual `Admitted.` placeholders with `Qed` proofs.
- Result: `remove_duplicates_sorted_proof_manual.v` compiles and contains no `Admitted.` or local `Axiom`.

## Issue 4: final compilation produced Coq intermediate files

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated`.
- Trigger: `coqc` emits these artifacts during the required full compile replay.
- Localization: `coq/generated/`.
- Fix action: after `goal_check` compiled successfully, deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `find coq -type f ! -name '*.v'` returns no files.
