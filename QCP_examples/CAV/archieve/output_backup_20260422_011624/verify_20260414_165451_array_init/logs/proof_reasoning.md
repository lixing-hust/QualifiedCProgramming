# Proof Reasoning

## Manual witness scope

After re-running `symexec`, the generated `proof_auto.v` provides placeholder lemmas for the safety and partial-solve witnesses, but it does not define these four obligations:

- `array_init_entail_wit_1`
- `array_init_return_wit_1`
- `array_init_which_implies_wit_1`
- `array_init_which_implies_wit_2`

These are the only witnesses that need to be implemented in `array_init_proof_manual.v` for `goal_check.v` to compile.

## Proof plan by witness

### `entail_wit_1`

This is the loop-entry normalization step. The goal is to show that the initial full array already matches the invariant instance at `i = 0`.

Planned steps:

- `pre_process`
- derive `n_pre = Zlength l` using `IntArray.full_length`
- unfold `zeros 0` to `nil`
- rewrite `app_nil_l`
- rewrite `sublist 0 n_pre l` to `l`
- finish with `entailer!`

### `return_wit_1`

This is the loop-exit normalization step. From `i >= n_pre` and `i <= n_pre`, first deduce `i = n_pre`. Then the invariant content becomes `app(zeros n_pre, sublist n_pre n_pre l)`, and the suffix is empty.

Planned steps:

- `pre_process`
- use `lia` to replace `i` with `n_pre`
- show `sublist n_pre n_pre l = []`
- rewrite `app_nil_r`
- close the entailment with `entailer!`

### `which_implies_wit_1`

This is the array-opening bridge assertion before the write. The core separation step is standard `IntArray.full_split_to_missing_i`. The only custom part is proving that the exposed cell value from the logical list
`app(zeros i, sublist i n_pre l)` equals `l[i]`.

Planned steps:

- `pre_process`
- `sep_apply (IntArray.full_split_to_missing_i a_pre i)`
- rewrite the exposed `Znth` through `app_Znth2`
- use `Zlength (zeros i) = i`
- rewrite the suffix value with `Znth_sublist`
- finish via `Znth_indep` and `entailer!`

### `which_implies_wit_2`

This is the fold-back step after writing `0`. The separation step is standard `IntArray.missing_i_merge_to_full`; the custom part is proving that replacing index `i` with `0` in
`app(zeros i, sublist i n_pre l)` produces `app(zeros(i + 1), sublist(i + 1, n_pre, l))`.

Planned steps:

- `pre_process`
- `sep_apply IntArray.missing_i_merge_to_full`
- rewrite with `replace_Znth_app_r`
- show the prefix `zeros i` is unchanged by replacement
- rewrite `zeros(i + 1)` as `zeros i ++ [0]`
- split `sublist i n_pre l` at `i + 1` using `sublist_split` and `sublist_single`
- conclude by reflexivity and `entailer!`

## Expected imports / tactics

The generated goal already imports the array strategy proof modules and list libraries, so the proof should only need:

- `pre_process`
- `sep_apply`
- `prop_apply`
- `entailer!`
- `lia`
- list lemmas such as `sublist_split`, `sublist_single`, `app_Znth2`, `Znth_sublist`, `replace_Znth_app_r`, `replace_Znth_nothing`
