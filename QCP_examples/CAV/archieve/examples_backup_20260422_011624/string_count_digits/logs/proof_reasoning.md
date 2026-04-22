# Proof reasoning

## 2026-04-20 initial manual proof plan

Current generated file: `coq/generated/string_count_digits_proof_manual.v`.

Observed obligations: `proof_of_string_count_digits_safety_wit_7`, `proof_of_string_count_digits_entail_wit_1`, `proof_of_string_count_digits_entail_wit_2_1`, `proof_of_string_count_digits_entail_wit_2_2`, `proof_of_string_count_digits_entail_wit_2_3`, and `proof_of_string_count_digits_entail_wit_3` were generated as `Admitted`.

The close examples `string_count_lowercase` and `string_count_spaces` have the same prefix/suffix invariant shape. The only semantic difference here is the digit classifier `48 <= x <= 57`, implemented in Coq as nested `Z_le_dec` tests. The proof therefore needs two local helpers:

- `string_count_digits_spec_range`, proving the count is between `0` and `Zlength l`; this is used for the increment overflow safety witness.
- `string_count_digits_spec_app_single`, proving how the recursive spec changes when appending one scanned character to the processed prefix.

For the three loop branch witnesses, the proof should destruct the remaining suffix `l2_2`, extract the current character `x` from the `CharArray.full` read fact using `app_Znth2`, and then update the existential processed prefix to `l1_2 ++ x :: nil`. The in-range branch proves the appended spec adds `1`; the low and high out-of-range branches prove it adds `0`.

For the exit witness, the proof first derives `i = n` from the sentinel read and the precondition that all positions `0 <= k < n` in `l` are nonzero. Then `Zlength(l1) == n`, `Zlength(l) == n`, and `l == app(l1, l2)` force `l2` to be empty, giving `cnt == string_count_digits_spec(l)`.
