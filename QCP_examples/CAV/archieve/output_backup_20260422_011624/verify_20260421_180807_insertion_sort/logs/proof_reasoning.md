
## 2026-04-21 proof phase start

- Generated manual obligations after the corrected annotations: `proof_of_insertion_sort_entail_wit_1`, `_2`, `_3`, `_4_1`, `_4_2`, and `return_wit_1`.
- `entail_wit_1` is the outer invariant initialization; it should use `l` as `l_outer` and prove that any one-element prefix is sorted.
- `entail_wit_2` initializes the inner invariant with `l_cur = l_outer` and `l_base = l_outer`; its hard pure point is normalizing `sublist(0, i + 1, l_outer) ++ sublist(i, i, l_outer) ++ sublist(i + 1, n, l_outer)` back to `l_outer` under the array length.
- `entail_wit_3`, `_4_1`, and `_4_2` are insertion-specific list update obligations around the shifted hole and final insertion. They likely need helper lemmas about `replace_Znth`, `sublist`, and preserving sortedness after inserting `key` into a sorted prefix.
- `return_wit_1` should use `l_outer` and show that `sorted_z(sublist(0, i, l_outer))` gives `sorted_z l_outer` when `i >= n_pre` and `IntArray::full` gives `Zlength l_outer = n_pre`; the skipped cases rely on the widened `i <= n_pre + 1` bound.

## 2026-04-21 retry proof iteration: inner shift witness

- Current blocker: `coq/generated/insertion_sort_proof_manual.v` still has admitted `proof_of_insertion_sort_entail_wit_3`, `_4_1`, and `_4_2`. Recompiling the current workspace succeeds only because those admissions remain; this is not workflow success.
- Focus theorem: `proof_of_insertion_sort_entail_wit_3`. After `pre_process`, `prop_apply IntArray.full_length`, choosing `l_base = l_base_2` and `l_cur = replace_Znth (j + 1) (Znth j l_cur_2 0) l_cur_2`, `entailer!` leaves two stable pure goals. First, the replacement list must equal the next hole representation `sublist 0 (j+1) l_base_2 ++ sublist j i_2 l_base_2 ++ sublist (i_2+1) n_pre l_base_2`. Second, the strengthened range fact for `j-1 < k < i_2` needs the new case `k = j`, which follows from the loop guard `Znth j l_cur_2 0 > key` once `Znth j l_cur_2 0 = Znth j l_base_2 0` is established.
- Next edit: add helper lemmas in `proof_manual.v` for replacing the last element of `p ++ [y]`, for reading `Znth j` from the current hole representation, and for normalizing one inner-loop shift. Then use them in `proof_of_insertion_sort_entail_wit_3`.

## 2026-04-21 retry proof iteration: regenerated goals after length invariant

- After adding `Zlength(l_outer) == n@pre` and `Zlength(l_base) == n@pre`, `symexec` succeeded at `2026-04-21T18:32:43+08:00` and regenerated all Coq files. The manual file was reset to six admitted witnesses, so the earlier local helper lemmas must be reintroduced against the fresh goal file.
- The new `entail_wit_3` now explicitly includes `Zlength l_base_2 = n_pre`, which removes the previous blocker where the shift lemma could not prove `n_pre = Zlength l_base_2` from the heap state. I will first restore the helper lemmas and complete `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, and `return_wit_1`, then inspect the remaining final insertion witnesses.

## 2026-04-21 retry proof iteration: helper lemma instantiation in final witnesses

- Current compile blocker: full `coqc` fails at `coq/generated/insertion_sort_proof_manual.v:557` with `Attempt to save an incomplete proof` in `proof_of_insertion_sort_entail_wit_4_1`.
- Proof-state inspection after the current script shows that the first three subgoals of `entailer!` are handled in intent: the heap cleanup goal is solved by two `store_int_undef_store_int` applications, the adjacent-order goal is discharged by `insertion_sort_final_adj_ge`, and the permutation goal reduces through `insertion_sort_final_perm`.
- The remaining open goal comes from the final length helper call. The script used `eapply insertion_sort_final_Zlength with (j := j) (i := i); try lia; try eauto; try (symmetry; exact H6)`, which left Coq free to instantiate the helper's `l_base` with the stale outer-loop list `l_outer_2` instead of the inner saved base list `l_base`. The resulting impossible side condition is:

```coq
l_cur =
  sublist 0 (j + 2) l_outer_2 ++
  sublist (j + 1) i l_outer_2 ++
  sublist (i + 1) n_pre l_outer_2
```

- The correct side condition is exactly the inner invariant hypothesis:

```coq
H10 :
  l_cur =
    sublist 0 (j + 2) l_base ++
    sublist (j + 1) i l_base ++
    sublist (i + 1) n_pre l_base
```

- Next proof edit: in both `proof_of_insertion_sort_entail_wit_4_1` and `_4_2`, pass `(l_base := l_base)` and `(l_cur := l_cur)` explicitly to every final insertion helper, and solve the structural side condition with `exact H10` rather than broad `eauto`/`symmetry` fallback. This preserves the existing helper lemmas and only fixes the witness scripts' instantiation ambiguity.

## 2026-04-21 retry proof completion: adjacent-order invariant

- Repair chosen: changed the annotation to carry adjacent prefix order instead of structural `sorted_z` through the loops, reran `symexec`, and rebuilt `proof_manual.v` against the regenerated goals.
- Added local helper lemmas for `replace_Znth` length, final insertion list shape, `Znth` reads in the inserted list, permutation of the inserted list against `l_base`, adjacent-order preservation for both `j >= 0` and `j < 0` final-write branches, and a return helper deriving `sorted_z` from adjacent order.
- The final insertion witness scripts now explicitly instantiate the helper lemmas with `(l_base := l_base)` and `(l_cur := l_cur)`, avoiding the previous ambiguity where Coq tried to use `l_outer_2`.
- Verification result: `proof_manual.v` compiles without `Admitted.`, and the full compile sequence through `insertion_sort_goal_check.v` succeeds.
