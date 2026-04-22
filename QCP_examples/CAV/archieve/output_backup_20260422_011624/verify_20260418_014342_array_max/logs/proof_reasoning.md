## Initial proof analysis

Generated manual goals:

- `proof_of_array_max_entail_wit_2_2`
- `proof_of_array_max_return_wit_1`

Both goals are pure list facts; they do not require extra separation-logic reasoning beyond `entailer!`.

For `entail_wit_2_2`, the missing fact is that extending the processed prefix from length `i` to length `i + 1` appends exactly `Znth i l 0`, and if that new element is `<=` the old prefix maximum then the maximum does not change.

For `return_wit_1`, the loop exit facts `i >= n_pre` and `i <= n_pre` force `i = n_pre`, after which the goal reduces to `sublist 0 (Zlength l) l = l`.

Plan:

1. Add a small helper lemma for `sublist 0 (i + 1) l`.
2. Add a helper lemma showing the max of `prefix ++ [x]` stays unchanged when `x <= current_max`.
3. Add a helper lemma `sublist 0 (Zlength l) l = l`.
4. Use these helpers in the two manual witness proofs and compile the generated files.
