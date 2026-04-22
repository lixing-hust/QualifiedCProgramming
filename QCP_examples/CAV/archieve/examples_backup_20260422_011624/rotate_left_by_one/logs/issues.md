# Verify Issues

## Missing loop invariant before first `symexec`

- Symptom: the active annotated file initially had no `Inv` for `for (i = 0; i + 1 < n; ++i)`.
- Trigger: verifying the loop requires a stable loop-head assertion; without it, the loop cannot preserve the in-place shift semantics.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260419_203636_rotate_left_by_one.c`, loop before the shift assignment.
- Fix: added an invariant with prefix list `l1`, facts `0 <= i <= n@pre - 1`, `first == l[0]`, and array contents `app(l1, sublist(i, n@pre, l))`.
- Result: `symexec` completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual proof obligations generated

- Symptom: `rotate_left_by_one_proof_manual.v` contained three `Admitted.` obligations after successful `symexec`: `entail_wit_1`, `entail_wit_2`, and `return_wit_1`.
- Trigger: the generated VCs needed list normalization for `sublist`, `app`, and `replace_Znth` that automation did not solve.
- Location: `output/verify_20260419_203636_rotate_left_by_one/coq/generated/rotate_left_by_one_proof_manual.v`.
- Fix: added two helper lemmas:
  - `rotate_left_by_one_step_list` for the loop-step array-content transformation.
  - `rotate_left_by_one_final_list` for the final write to `a[n - 1]`.
- Result: all three manual obligations were proven and `proof_manual.v` contains no `Admitted.` proof or newly added `Axiom`.

## Proof-script rewrite side conditions

- Symptom: early compilation of `proof_manual.v` failed in the helper lemma with `Cannot find witness` at a `sublist_split` rewrite.
- Trigger: `lia` did not have the concrete `Zlength_correct l` fact needed by the rewrite side condition.
- Location: `rotate_left_by_one_step_list` in `rotate_left_by_one_proof_manual.v`.
- Fix: supplied `pose proof (Zlength_correct l); lia` for `sublist_split` and `sublist_single` side conditions.
- Result: the helper advanced past the sublist split.

## Prefix replacement after `replace_Znth_app_r`

- Symptom: compiling `rotate_left_by_one_step_list` next failed because Coq could not unify the expected appended prefix with a residual `replace_Znth i ... l1`.
- Trigger: `replace_Znth_app_r` preserves a prefix replacement term when the write index is exactly `Zlength l1`.
- Location: `rotate_left_by_one_step_list`.
- Fix: rewrote the residual prefix replacement using `replace_Znth_nothing` under `Zlength l1 = i`.
- Result: the loop-step helper compiled.

## Return witness normalized around `Zlength l1`

- Symptom: applying `rotate_left_by_one_final_list` in `return_wit_1` initially failed because the memory term contained `sublist (Zlength l1) n_pre l`, not syntactic `sublist (n_pre - 1) n_pre l`.
- Trigger: `pre_process` normalized the exit index through the prefix length.
- Location: `proof_of_rotate_left_by_one_return_wit_1`.
- Fix: after rewriting `first = Znth 0 l 0`, rewrote `Zlength l1 = n_pre - 1` before applying the helper lemma.
- Result: the memory assertion matched the helper lemma, and the remaining pure postcondition goals were discharged.

## Final compile and cleanup

- Symptom: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` intermediate files under `coq/generated/`.
- Trigger: normal `coqc` output.
- Location: `output/verify_20260419_203636_rotate_left_by_one/coq/generated/`.
- Fix: deleted all non-`.v` files under `coq/`.
- Result: `coq/` contains only `.v` source files after cleanup.
