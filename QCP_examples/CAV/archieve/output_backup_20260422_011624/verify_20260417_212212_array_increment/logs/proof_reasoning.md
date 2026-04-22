First pass over `array_increment_goal.v` shows seven manual obligations:

- `safety_wit_2/3/4`: pure arithmetic bounds produced by the write and loop increment
- `entail_wit_1`: initialize the invariant with empty processed prefix and full suffix
- `entail_wit_2`: re-establish the invariant after one write
- `entail_wit_3`: discharge the loop-exit assertion into the function postcondition
- `return_wit_1`: package the exit witness for the function return
- `which_implies_wit_1/2`: split and merge the array around index `i`

The closest reusable proof patterns are the existing `set_zero` and `copy_array` manual proofs:

- `which_implies_wit_1` uses `IntArray.full_split_to_missing_i` and a `Znth` rewrite over `app`
- `which_implies_wit_2` uses `IntArray.missing_i_merge_to_full` plus a `replace_Znth` characterization of the updated list
- `entail_wit_1`, `entail_wit_2`, and `return_wit_1` are mostly witness selection, `Zlength` arithmetic, and `sublist` normalization

Planned proof structure:

- start each lemma with `pre_process`
- use `lia` for the safety witnesses
- use `Exists` for existential witnesses in the entail/return/which-implies goals
- normalize list lengths with `rewrite Zlength_correct in *`
- use `sublist` lemmas to characterize the suffix after index `i + 1`
- use `replace_Znth` to show the concrete array after the store matches the logical updated list
