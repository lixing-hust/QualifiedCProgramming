## 2026-04-20 manual proof plan

- Generated manual file contains six admitted witnesses: safety_wit_2, entail_wit_1, entail_wit_2, return_wit_1, which_implies_wit_1, and which_implies_wit_2.
- The witness set and annotation shape match the completed CAV/examples/array_add proof. I will adapt that proof script by renaming the theorem and goal identifiers to array_pairwise_sum while keeping the same explicit list-normalization steps.
- Expected blocker class: pure list and arithmetic side conditions around extending the processed output prefix and rebuilding IntArray::full from missing_i/data_at.

## 2026-04-20 proof completion

- Filled all six manual witnesses in `coq/generated/array_pairwise_sum_proof_manual.v`.
- `proof_of_array_pairwise_sum_safety_wit_2` uses the contract overflow hypothesis at the current loop index `i` and the invariant range `0 <= i < n_pre`.
- `proof_of_array_pairwise_sum_entail_wit_1` packages the initial invariant with empty processed prefix and original `lo` suffix.
- `proof_of_array_pairwise_sum_entail_wit_2` packages the next-loop invariant after the write, using `sublist (i_2 + 1) n_pre lo` for the remaining suffix.
- `proof_of_array_pairwise_sum_return_wit_1` derives `i_3 = n_pre`, proves the remaining suffix list is `nil`, chooses `l1` as the result list, and discharges the postcondition pointwise.
- `proof_of_array_pairwise_sum_which_implies_wit_1` splits the three full arrays at index `i` with `IntArray.full_split_to_missing_i` and proves the old output cell is `lo[i]` from the suffix relation.
- `proof_of_array_pairwise_sum_which_implies_wit_2` merges the focused cells back to full arrays, proves `l2 = sublist i n_pre lo`, normalizes the updated output list to `l1 ++ cons (la[i] + lb[i]) nil ++ sublist (i + 1) n_pre lo`, and proves the extended prefix property plus length fact.
- Full compile replay succeeded for `array_pairwise_sum_goal.v`, `array_pairwise_sum_proof_auto.v`, `array_pairwise_sum_proof_manual.v`, and `array_pairwise_sum_goal_check.v`.
- Final grep found no `Admitted.` and no top-level `Axiom` declarations in `array_pairwise_sum_proof_manual.v`.
