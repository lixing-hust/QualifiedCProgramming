# Proof Reasoning

## Round 1

- Fresh `symexec` succeeded on the latest active annotated file and generated `upper_bound_goal.v`, `upper_bound_proof_auto.v`, `upper_bound_proof_manual.v`, and `upper_bound_goal_check.v`.
- The generated `upper_bound_proof_manual.v` contains six admitted manual obligations: `proof_of_upper_bound_safety_wit_2`, `proof_of_upper_bound_entail_wit_1`, `proof_of_upper_bound_entail_wit_2`, `proof_of_upper_bound_entail_wit_3`, `proof_of_upper_bound_entail_wit_4_1`, and `proof_of_upper_bound_entail_wit_4_2`.
- `upper_bound_proof_auto.v` contains generated admitted auto lemmas, including return and partial-solve witnesses. Those are not manually edited; completion will rely on Coq accepting the generated auto module and on removing all `Admitted.` from the manual proof file.
- Close reusable pattern: `CAV/examples/lower_bound/coq/generated/lower_bound_proof_manual.v` has the same binary-search midpoint arithmetic and half-open interval preservation witnesses.
- Planned proof:
  - add local helper lemmas for `x ÷ 2` bounds and strict upper bound when `x > 0`;
  - prove `safety_wit_2` by recovering stack integer ranges for `left` and `right`, then using quotient bounds;
  - prove midpoint bridge `entail_wit_2` using quotient bounds and strict quotient;
  - prove `entail_wit_4_1` by building the new upper suffix `forall j, mid <= j < n_pre -> Znth j l 0 > target_pre`, using sortedness for `j > mid`;
  - prove `entail_wit_4_2` by building the new lower prefix `forall j, 0 <= j < mid + 1 -> Znth j l 0 <= target_pre`, using sortedness for `j <= mid`;
  - use `store_int_undef_store_int` for the local `mid` slot when the invariant re-entails it as undefined.
