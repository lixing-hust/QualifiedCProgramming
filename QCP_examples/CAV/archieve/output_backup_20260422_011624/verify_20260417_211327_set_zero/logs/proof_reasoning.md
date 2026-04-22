# Proof Reasoning

## Manual witness scope

After `symexec`, `set_zero_proof_manual.v` still contains four admitted obligations:

- `set_zero_entail_wit_1`
- `set_zero_return_wit_1`
- `set_zero_which_implies_wit_1`
- `set_zero_which_implies_wit_2`

These are the only manual witnesses needed for `goal_check.v`.

## Proof plan by witness

### `entail_wit_1`

This is the loop-entry normalization. The initial full-array resource should already match the invariant at `i = 0`, so the proof only needs to normalize `zeros 0` and `sublist 0 n_pre l`.

### `return_wit_1`

This is the loop-exit normalization. From `i >= n_pre` and `i <= n_pre`, derive `i = n_pre`, then simplify the suffix `sublist n_pre n_pre l` to `nil`.

### `which_implies_wit_1`

This is the pre-store bridge assertion. The main separation step is `IntArray.full_split_to_missing_i`; the only extra work is rewriting the exposed cell from the logical list `zeros i ++ sublist i n_pre l` back to `l[i]`.

### `which_implies_wit_2`

This is the post-store fold-back step. Use `IntArray.missing_i_merge_to_full`, then prove that replacing index `i` with `0` in `zeros i ++ sublist i n_pre l` yields `zeros (i + 1) ++ sublist (i + 1) n_pre l`.

## Expected tactics

The proof should close with the same small tactic set as the prior zero-fill example:

- `pre_process`
- `sep_apply`
- `prop_apply`
- `entailer!`
- `lia`
- list rewrites around `sublist`, `Znth`, and `replace_Znth`
