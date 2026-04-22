## Proof reasoning - initial manual obligations after successful symexec

Fresh symexec succeeded and generated `array_move_zeroes_to_end_goal.v`, `array_move_zeroes_to_end_proof_auto.v`, `array_move_zeroes_to_end_proof_manual.v`, and `array_move_zeroes_to_end_goal_check.v`. The generated manual file currently contains seven admitted lemmas:

- `proof_of_array_move_zeroes_to_end_entail_wit_1`: initialization of the first-loop invariant, expected witness `lc = l`; pure obligations are empty-prefix/sublist facts and the heap is unchanged.
- `proof_of_array_move_zeroes_to_end_entail_wit_2_1`: first-loop preservation in the nonzero branch after writing `a[write] = a[i]`; expected witness is the updated array list from the heap, with core pure work about `move_zeroes_nonzeroes (sublist 0 (i+1) l)` extending by `l[i]`.
- `proof_of_array_move_zeroes_to_end_entail_wit_2_2`: first-loop preservation in the zero branch; expected witness `lc_2`, with pure work showing the nonzero-prefix summary is unchanged when `l[i] = 0`.
- `proof_of_array_move_zeroes_to_end_entail_wit_3`: transition from the first loop to the second loop; expected witness `lc`, using `i >= n_pre` and `i <= n_pre` to get `i = n_pre`, then normalizing `sublist 0 n_pre l` to `l`.
- `proof_of_array_move_zeroes_to_end_return_wit_1`: final postcondition after the zero-fill loop; expected pure/list work is to show `lc_2 = move_zeroes_to_end_spec l` from prefix facts plus zero suffix facts and the length relation.
- `proof_of_array_move_zeroes_to_end_which_implies_wit_1`: bridge from `IntArray.full` to `missing_i + data_at` at `write`; this should be handled by the array strategy plus `entailer!`.
- `proof_of_array_move_zeroes_to_end_which_implies_wit_2`: bridge from `missing_i + data_at 0` back to an existential full array; expected witness is the list obtained by replacing index `write` with `0`.

First proof attempt: use the standard skeleton `pre_process; entailer!` for the simple initialization/bridge obligations and instantiate obvious witnesses (`l`, `lc`, `lc1`) where the goal is structurally an existential. If this fails, I will inspect the exact failed theorem with `coqtop` and then add helper lemmas for the nonzero-prefix and final list equality obligations.

## Proof reasoning - first compile failure

The first replacement of `Admitted.` compiled through generated goal and proof_auto, then failed in `array_move_zeroes_to_end_proof_manual.v` line 27:
```text
Error: No such goal.
```

The failing proof was:
```coq
Proof.
  pre_process.
  Exists l.
  entailer!.
  rewrite sublist_nil; simpl; lia.
Qed.
```

`entailer!` had already solved `entail_wit_1` after choosing `lc = l`, so the extra rewrite ran after all goals were closed. The fix is to delete the redundant rewrite and keep the minimal proof for `entail_wit_1`.

## Proof reasoning - `entail_wit_2_1` proof state

Direct `coqtop` inspection after:
```coq
pre_process.
Exists (replace_Znth write (Znth i lc_2 0) lc_2).
entailer!.
Show.
```

left four pure goals:
```text
1. forall k_2, i + 1 <= k_2 < n_pre ->
     Znth k_2 (replace_Znth write (Znth i lc_2 0) lc_2) 0 = Znth k_2 l 0
2. forall k, 0 <= k < write + 1 ->
     Znth k (replace_Znth write (Znth i lc_2 0) lc_2) 0 =
     Znth k (move_zeroes_nonzeroes (sublist 0 (i + 1) l)) 0
3. write + 1 = Zlength (move_zeroes_nonzeroes (sublist 0 (i + 1) l))
4. Zlength (replace_Znth write (Znth i lc_2 0) lc_2) = n_pre
```

The needed facts are reusable: `replace_Znth` preserves length, `Znth` of a replaced list is the new value at the replaced index and the old value elsewhere, and `move_zeroes_nonzeroes (xs ++ [x])` appends `x` exactly when `x <> 0`. I will add these helper lemmas before the manual witness proofs, then use them in both first-loop branch witnesses. The nonzero branch additionally uses `sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0]`, obtained by `sublist_split` and `sublist_single`, and `H9 i` to convert `Znth i lc_2 0 <> 0` into `Znth i l 0 <> 0`.

## Proof reasoning - final proof shape and compile result

The final `array_move_zeroes_to_end_proof_manual.v` removes all manual `Admitted.` placeholders and adds only local helper lemmas needed by this task:

```coq
amz_replace_nth_length
amz_nth_replace_nth_eq
amz_nth_a_replace_nth_b
amz_replace_Znth_length
amz_Znth_replace_Znth_eq
amz_Znth_replace_Znth_other
amz_nonzeroes_snoc_nonzero
amz_nonzeroes_snoc_zero
amz_zeroes_snoc_nonzero
amz_zeroes_snoc_zero
amz_lengths
amz_spec_length
amz_Znth_zeroes_zero
```

The first-loop nonzero branch proof chooses:

```coq
replace_Znth write (Znth i lc_2 0) lc_2
```

as the next logical array. It proves the next nonzero-prefix summary by splitting the scanned prefix:

```coq
sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]
```

then applying `amz_nonzeroes_snoc_nonzero`. The zero branch uses the same prefix split and `amz_nonzeroes_snoc_zero`. The first-to-second loop transition first proves `i = n_pre`, rewrites `sublist 0 n_pre l` to `l`, and observes the second-loop zero range is initially empty because `write = Zlength(move_zeroes_nonzeroes l)`.

The return witness proves `write_2 = n_pre`, then proves `lc_2 = move_zeroes_to_end_spec l` by `list_eq_ext`: indices before `Zlength(move_zeroes_nonzeroes l)` come from the nonzero prefix invariant, and suffix indices come from the zero-filled invariant plus `amz_Znth_zeroes_zero`.

The two `which_implies` bridge proofs use the stable array lemmas:

```coq
IntArray.full_split_to_missing_i
IntArray.missing_i_merge_to_full
```

Both need an explicit range fact:

```coq
0 <= write < n_pre
```

which follows from `Zlength_nonneg (move_zeroes_nonzeroes l)`, `Zlength(move_zeroes_nonzeroes l) <= write`, and `write < n_pre`.

Full compile replay from `/home/yangfp/QualifiedCProgramming/SeparationLogic` passed for:

```text
original/array_move_zeroes_to_end.v
coq/generated/array_move_zeroes_to_end_goal.v
coq/generated/array_move_zeroes_to_end_proof_auto.v
coq/generated/array_move_zeroes_to_end_proof_manual.v
coq/generated/array_move_zeroes_to_end_goal_check.v
```

Final checks:

```text
grep -RIn "Admitted\\.\\|^Axiom" coq/generated/array_move_zeroes_to_end_proof_manual.v
```

reported no `Admitted.` and no newly added top-level `Axiom`. After compilation, all non-`.v` files under `output/verify_20260422_000928_array_move_zeroes_to_end/coq/` were deleted.
