# Proof Reasoning

## Iteration 1: manual obligations after successful symexec

- Fresh `symexec` succeeded for `annotated/verify_20260421_041506_binary_search_first.c` and generated `binary_search_first_goal.v`, `binary_search_first_proof_auto.v`, `binary_search_first_proof_manual.v`, and `binary_search_first_goal_check.v`.
- `binary_search_first_proof_manual.v` contains seven admitted obligations:
  - `proof_of_binary_search_first_safety_wit_2`;
  - `proof_of_binary_search_first_entail_wit_1`;
  - `proof_of_binary_search_first_entail_wit_2`;
  - `proof_of_binary_search_first_entail_wit_3`;
  - `proof_of_binary_search_first_entail_wit_4_1`;
  - `proof_of_binary_search_first_entail_wit_4_2`;
  - `proof_of_binary_search_first_return_wit_2`.
- The first six match the proof shape from the nearby `lower_bound` example: quotient-by-2 midpoint arithmetic, direct assertion entailments, and loop-invariant preservation for the two branches. I will reuse the same local helper lemmas and branch proof pattern, renaming only the witness prefix.
- The remaining return witness is specific to `binary_search_first`: on the branch where `left < n` but `a[left] != target`, the proof must show every array element is not target. The available facts include `left >= right`, `left <= right` so `left = right`, the lower prefix fact `j < left -> l[j] < target`, the point fact `l[left] >= target`, the failed equality at `left`, and sortedness. The planned proof constructs a `forall i` split:
  - `i < left`: use the strict-less prefix;
  - `i = left`: use the branch condition `Znth left l 0 <> target`;
  - `left < i`: use sortedness from `left` to `i`, plus `Znth left l 0 >= target` and `Znth left l 0 <> target`, to show `target < Znth i l 0`.

## Iteration 2: return witness disjunction

- First compile of the edited manual proof reached `proof_of_binary_search_first_return_wit_2` and failed at the final `Qed` with `Attempt to save an incomplete proof`.
- Inspecting the post-`entailer!` state showed the remaining goal was the separation-logic disjunction for the postcondition. The left branch is impossible because it asks for `0 <= -1`; the proof had built the `forall i` needed by the right branch but had not explicitly selected that branch.
- Fix: add `right.` immediately before the final `entailer!` in `proof_of_binary_search_first_return_wit_2`, matching the disjunctive return-witness pattern used in existing examples such as `is_sorted_nondecreasing`.
