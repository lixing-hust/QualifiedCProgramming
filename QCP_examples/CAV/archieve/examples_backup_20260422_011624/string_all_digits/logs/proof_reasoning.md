# Proof Reasoning

## Round 1

- `symexec` succeeded on the current annotated file and generated five admitted manual obligations: `proof_of_string_all_digits_entail_wit_1`, `proof_of_string_all_digits_entail_wit_2`, `proof_of_string_all_digits_return_wit_1`, `proof_of_string_all_digits_return_wit_2`, and `proof_of_string_all_digits_return_wit_3`.
- The obligations mirror the existing verified `string_all_lowercase` pattern, with ASCII bounds changed from `[97,122]` to `[48,57]`.
- `entail_wit_1` initializes the invariant with `l1 = nil` and `l2 = l`.
- `entail_wit_2` preserves the invariant after one successful digit check by moving the head of `l2` into the processed prefix.
- `return_wit_1` and `return_wit_2` prove the recursive spec returns `0` for a current character above `57` or below `48`.
- `return_wit_3` proves the final return value is `1`; the key bridge is deriving `i = n` from the observed terminator and the contract fact that all positions `< n` are nonzero.
- Planned proof edit: add three local helper lemmas for append-preservation and bad-character cases, then replace each admitted witness with the corresponding short proof adapted from the lowercase example.

## Round 2

- After adding the helper lemmas and five witness proofs, the documented compile chain succeeded:
  - `original/string_all_digits.v`
  - `coq/generated/string_all_digits_goal.v`
  - `coq/generated/string_all_digits_proof_auto.v`
  - `coq/generated/string_all_digits_proof_manual.v`
  - `coq/generated/string_all_digits_goal_check.v`
- The helper lemmas used in `proof_manual.v` are:
  - `string_all_digits_spec_app_digit` for the loop-preservation branch where the current character is in `[48,57]`
  - `string_all_digits_spec_app_bad_high` for the early return where the current character is above `57`
  - `string_all_digits_spec_app_bad_low` for the early return where the current character is below `48`
- `return_wit_3` was discharged by first deriving `i = n` from `Znth i (l ++ [0]) = 0` plus the contract fact that every `l[k]` for `0 <= k < n` is nonzero.
- A final grep found no `Admitted.` declarations and no new `Axiom` declarations in `coq/generated/string_all_digits_proof_manual.v`; the only occurrence of the word `Axioms` is the existing import from `AUXLib`.
