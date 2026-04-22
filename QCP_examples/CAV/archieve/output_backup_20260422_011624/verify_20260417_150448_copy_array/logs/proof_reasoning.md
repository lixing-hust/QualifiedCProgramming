# Proof Reasoning

## Remaining manual goals

`copy_array_proof_manual.v` contains four admitted lemmas:

- `proof_of_copy_array_entail_wit_1`
- `proof_of_copy_array_return_wit_1`
- `proof_of_copy_array_which_implies_wit_1`
- `proof_of_copy_array_which_implies_wit_2`

They are all standard list/array-shape obligations generated from the loop invariant and bridge assertions.

## Planned proof patterns

`entail_wit_1`

- Show that the invariant holds at loop entry with `i = 0`.
- Rewrite `app(sublist(0,0,ls), sublist(0,n,ld))` to `ld`.
- This should be a short `pre_process` proof with `sublist` simplification and `app_nil_l`.

`return_wit_1`

- From loop exit, pure facts give `i = n_pre`.
- Rewrite the destination list
  `app(sublist(0,i,ls), sublist(i,n_pre,ld))`
  to
  `app(sublist(0,n_pre,ls), sublist(n_pre,n_pre,ld))`
  and then to `ls`.
- This is the same shape as the array-init exit proof, but the copied prefix is `ls` instead of `zeros`.

`which_implies_wit_1`

- Split both full arrays at index `i` using `IntArray.full_split_to_missing_i`.
- For the destination cell, prove that the `i`-th element of
  `app(sublist(0,i,ls), sublist(i,n_pre,ld))`
  is exactly `ld[i]`.
- This is an `app_Znth2` plus `Znth_sublist` argument.

`which_implies_wit_2`

- Merge the `src` missing-cell decomposition back to `IntArray.full src_pre n_pre ls`.
- Merge the `dst` missing-cell decomposition back to a full array using `IntArray.missing_i_merge_to_full`.
- Then rewrite the resulting `replace_Znth` list into
  `app(sublist(0,i+1,ls), sublist(i+1,n_pre,ld))`
  using `replace_Znth_app_r`, `replace_Znth_nothing`, `sublist_split`, and `sublist_single`.

## Expected difficulty

No new auxiliary theorem should be necessary. The only nontrivial algebra is the destination-list rewrite after the store, and the repo already uses the same rewrite scheme in `array_init_proof_manual.v`.
