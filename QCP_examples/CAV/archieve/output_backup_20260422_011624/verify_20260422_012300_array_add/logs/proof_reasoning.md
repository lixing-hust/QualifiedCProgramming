# Proof Reasoning

## Round 1

- Read `array_add_goal.v`, `array_add_proof_auto.v`, and `array_add_goal_check.v`.
- Manual obligations are:
  - `proof_of_array_add_safety_wit_2`
  - `proof_of_array_add_entail_wit_1`
  - `proof_of_array_add_entail_wit_2`
  - `proof_of_array_add_return_wit_1`
  - `proof_of_array_add_which_implies_wit_1`
  - `proof_of_array_add_which_implies_wit_2`
- The generated shapes suggest a low-risk first attempt:
  - safety witness should be pure range extraction from the contract hypothesis
  - entail witnesses should be existential packaging of the invariant state
  - return witness should take `lr = l1` after deriving `i = n_pre`
  - `which implies` witnesses should be handled mostly by the array strategy plus the bridge facts already present in the annotation
- Initial proof plan:
  - start with `pre_process`
  - follow with `entailer!`
  - use `lia` only for remaining pure arithmetic
  - only inspect detailed proof states if one of these witnesses does not close under that conservative pattern

## Round 2

- `safety_wit_2`, `entail_wit_1`, `entail_wit_2`, `return_wit_1`, and `which_implies_wit_1` all reduced after targeted proof-state inspection.
- The stable fixes were:
  - extract the range fact for `safety_wit_2` directly from the contract hypothesis instead of hoping `entailer!` would instantiate it
  - choose existential witnesses in the generated order (`l2` first, then `l1`) for the entail lemmas
  - prove `l2 = nil` at loop exit so the return witness can rewrite `app l1 l2` back to `l1`
  - replace the first bridge with explicit `full_split_to_missing_i` steps and a pointwise proof that the old output cell equals `lo[i]`

## Round 3

- The only remaining blocker is `proof_of_array_add_which_implies_wit_2`.
- Current understanding:
  - the source arrays are easy: `missing_i_merge_to_full` turns them into `IntArray.full ... (replace_Znth i (Znth i la 0) la)` and the same for `lb`, which can be normalized by `replace_Znth_Znth`
  - the destination array is the hard part: after merging, the heap still needs to be rewritten from the updated full list into the exact target shape
    `app(l1 ++ [la[i] + lb[i]], sublist(i + 1, n_pre, lo))`
- I proved the useful intermediate fact
  `l2 = sublist i n_pre lo`
  from `Zlength l2 = n_pre - i` plus the pointwise suffix relation, so the blocker is no longer about identifying the untouched suffix.
- The unresolved step is the final output-list normalization after the destination merge:
  - split `sublist i n_pre lo` into the head cell and tail suffix
  - rewrite the merged destination list into the prefix-extended target list
  - then discharge the final pure prefix-property goal
- At the time of stopping, `coqc` was still failing inside that theorem, so the workspace cannot be marked successful.

## Round 4

- Reopened `proof_of_array_add_which_implies_wit_2` and inspected the post-`entailer!` state with `coqtop`.
- The decisive observation was that the heap part was already solved after:
  - proving `l2 = sublist i n_pre lo`
  - rewriting the destination update into `l1 ++ (new :: sublist (i + 1) n_pre lo)`
- After that normalization, the theorem no longer needed any separation-logic reasoning. The remaining goals were only:
  - the extended prefix pointwise property for indices `0 <= k < i + 1`
  - the length fact `Zlength (l1 ++ [new]) = i + 1`
- The proof was completed by:
  - keeping the old prefix unchanged with `replace_Znth i ... l1 = l1`
  - isolating the written head cell with a direct `replace_Znth 0 ...`
  - splitting the pointwise proof into `k < i` and `k = i`
  - proving the length goal directly after the normalized list shape appeared
- After this change:
  - `array_add_proof_manual.v` compiled successfully
  - `array_add_goal_check.v` compiled successfully
- This confirms the previous failure was not a contract gap. It was a final list-shape normalization issue inside `which_implies_wit_2`.
