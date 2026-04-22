# Proof Reasoning

## Iteration 1: Complete prefix-count witnesses

- Current generated manual file:
  - `coq/generated/array_count_zero_proof_manual.v`
- Manual obligations:
  - `proof_of_array_count_zero_safety_wit_4`
  - `proof_of_array_count_zero_entail_wit_1`
  - `proof_of_array_count_zero_entail_wit_2_1`
  - `proof_of_array_count_zero_entail_wit_2_2`
  - `proof_of_array_count_zero_entail_wit_3`
- Current blocker:
  - all five manual lemmas are generated as `Admitted.`
  - the core pure fact needed by the preservation witnesses is that extending `sublist 0 i l` with `Znth i l 0` updates `array_count_zero_spec` by either `+ 1` or `+ 0`
  - the overflow safety witness for `count + 1` also needs a bound `0 <= array_count_zero_spec(prefix) <= Zlength(prefix)`, combined with `i < n_pre` and the stored C integer range for `n`
- Planned proof edits:
  - add helper lemma `array_count_zero_spec_app_single`
  - add helper lemma `array_count_zero_spec_bounds`
  - prove `safety_wit_4` by `pre_process`, `store_int_range (&("n")) n_pre`, the bounds lemma on `sublist 0 i l`, and `entailer!`
  - prove the two loop-preservation witnesses by splitting `sublist 0 (i + 1) l` at `i`, rewriting the singleton sublist, and case-splitting `Z.eq_dec`
  - prove the exit witness by deriving `i = n_pre`, rewriting `sublist 0 n_pre l` to `l`, and finishing the separation entailment
- Similar example:
  - `examples/count_equal_to_k/coq/generated/count_equal_to_k_proof_manual.v` has the same proof structure with an extra parameter `k`; this task is the `k = 0` specialization
