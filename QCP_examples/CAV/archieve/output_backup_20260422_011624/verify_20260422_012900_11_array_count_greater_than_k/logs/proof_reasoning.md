# Proof Reasoning

## Round 1

- Fresh `symexec` generated five manual obligations in `coq/generated/array_count_greater_than_k_proof_manual.v`: `proof_of_array_count_greater_than_k_safety_wit_3`, `proof_of_array_count_greater_than_k_entail_wit_1`, `proof_of_array_count_greater_than_k_entail_wit_2_1`, `proof_of_array_count_greater_than_k_entail_wit_2_2`, and `proof_of_array_count_greater_than_k_entail_wit_3`.
- Current blocker: all five generated lemmas are still `Admitted.`, so the manual file cannot satisfy the verify completion rule.
- Closest reusable pattern: `examples/count_equal_to_k/coq/generated/count_equal_to_k_proof_manual.v` has the same prefix-count invariant with an extra scalar parameter `k`. The only semantic difference is the singleton contribution test: this task uses `Z_gt_dec x k` instead of `Z.eq_dec x k`.
- Needed helper facts:
  - append-singleton lemma for `array_count_greater_than_k_spec (l ++ x :: nil)`;
  - bounds lemma `0 <= array_count_greater_than_k_spec l k <= Zlength l` for the `cnt + 1` overflow witness.
- Planned proof edits: add the two helper lemmas in the manual proof file, prove `safety_wit_3` using `store_int_range` for `n` plus the bounds lemma on the processed prefix, and prove the two loop-step entailments by splitting `sublist 0 (i + 1) l` at `i` and simplifying the singleton contribution under the branch condition.
