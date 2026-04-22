## Manual proof plan for `array_min`

The generated `proof_manual.v` contains exactly two manual obligations:

- `proof_of_array_min_entail_wit_2_2`
- `proof_of_array_min_return_wit_1`

The shape matches `array_max`, but with the order facts reversed.
So the intended proof pattern is:

1. Reuse a generic lemma `sublist 0 (Zlength l) l = l` for the return witness.
2. Prove that extending a nonempty list by an element `x` that is greater than or equal to the current minimum preserves `min_list_nonempty`.
3. Use `sublist_split` and `sublist_single` to rewrite the processed prefix at `i + 1` into the old prefix plus the new element `Znth i l 0`.

The nontrivial direction is `entail_wit_2_2`, where the witness assumption provides
`min_list_nonempty (sublist 0 i l) <= Znth i l 0`.
That is enough to show appending the new element does not change the current minimum.

The return witness should then collapse by substituting `i = n_pre`, rewriting `n_pre` to `Zlength l`, and using the full-sublist lemma.

## Iteration notes

- First compile failure: using `Z.min_glb_l` / `Z.min_glb_r` in `min_list_nonempty_lower_bound` left an unresolved implicit argument. Replaced them with the direct order lemmas `Z.le_min_l` / `Z.le_min_r`.
- Second compile failure: the first version of `min_list_nonempty_extend_le` tried to reuse `min_list_nonempty_lower_bound` directly, but that only shows the new global minimum is below a chosen element, not specifically below the old prefix minimum. Replaced it with an induction proof parallel to the working `array_max` pattern.
- Third compile failure: the boundedness proof for `min_list_nonempty_extend_keep` used the wrong transitivity direction on the prefix branch. Simplified that branch to `min_list_nonempty_lower_bound` directly and kept `Hx` only for the appended-element branch.
- Final compile adjustment: `entail_wit_2_2` carried the hypothesis as `Znth i l 0 >= min_list_nonempty (...)`, so the proof step was normalized with `lia` instead of relying on syntactic equality between `>=` and `<=`.
- After these changes, `array_min_proof_manual.v` and `array_min_goal_check.v` both compiled successfully.
