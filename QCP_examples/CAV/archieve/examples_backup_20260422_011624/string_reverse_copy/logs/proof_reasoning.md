# Proof Reasoning

## Round 1

- Read `string_reverse_copy_goal.v`, `string_reverse_copy_proof_auto.v`, and `string_reverse_copy_goal_check.v`.
- Generated manual obligations:
  - `proof_of_string_reverse_copy_entail_wit_1`
  - `proof_of_string_reverse_copy_entail_wit_2`
  - `proof_of_string_reverse_copy_return_wit_1`
- Classification:
  - `entail_wit_1` is the loop-initialization witness
  - `entail_wit_2` is the loop-preservation witness after writing one mirrored source character
  - `return_wit_1` is the final postcondition after writing the terminator
- Expected proof pattern:
  - reuse the same structure as the completed `string_copy` proof
  - for the reverse-specific part, add one small helper lemma showing
    - `Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0`
    - under the usual in-range side conditions

## First proof plan

- `entail_wit_1`:
  - choose `l1 = nil`
  - choose `d1 = d`
  - use `CharArray.full_length` only to discharge the required destination-length equality
- `entail_wit_2`:
  - choose `l1 = l1_2 ++ [Znth (n_pre - 1 - i) l 0]`
  - choose `d1 = tl d1_2`
  - normalize the updated destination list with `replace_Znth_app_r` and `replace_Znth_nothing`
  - prove the new prefix property by splitting `k < i + 1` into `k < i` or `k = i`
- `return_wit_1`:
  - derive `i = n_pre` from `i >= n_pre` and `i <= n_pre`
  - derive `l1 = rev l` by list extensionality using the invariant’s pointwise reverse-prefix fact and the helper lemma on `rev`
  - show `d1` has length `1`, normalize `replace_Znth n_pre 0 (l1 ++ d1)`, and finish with `entailer!`

## Round 2

- `entail_wit_1` and `entail_wit_2` followed the expected `string_copy` pattern after one correction:
  - the mirrored source read is still inside `l`, so the normalization step must use `app_Znth1`, not `app_Znth2`
- `return_wit_1` took several compile-guided iterations but stayed in the pure proof layer:
  - first stable subgoal: prove `l1 = rev l`
  - fix: add `Znth_rev_Z` and use `list_eq_ext`
  - second stable subgoal: make the final `replace_Znth` normalization expose index `0` on the one-cell suffix
  - fix: keep the tail witness as `x :: nil`, use `replace_Znth_app_r`, `replace_Znth_nothing`, and the length equality `Zlength (rev l) = n_pre`
- Final proof status:
  - `string_reverse_copy_proof_manual.v` compiles
  - `string_reverse_copy_goal_check.v` compiles
  - `string_reverse_copy_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`

## Final proof shape

- Local helper:
  - `Znth_rev_Z`
- Witness proofs:
  - `entail_wit_1`: initialize the destination split with `l1 = nil`
  - `entail_wit_2`: extend the processed prefix with `l[n_pre - 1 - i]`
  - `return_wit_1`: identify the processed prefix with `rev l`, reduce the remaining suffix to one cell, and normalize the terminating store to `rev l ++ [0]`
