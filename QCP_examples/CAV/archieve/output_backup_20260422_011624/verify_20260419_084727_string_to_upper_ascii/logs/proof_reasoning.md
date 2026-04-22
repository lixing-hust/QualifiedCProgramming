# Proof Reasoning

## Round 1: generated manual obligations

- After successful `symexec`, `coq/generated/string_to_upper_ascii_proof_manual.v` contains five admitted obligations:
  - `proof_of_string_to_upper_ascii_entail_wit_1`
  - `proof_of_string_to_upper_ascii_entail_wit_2_1`
  - `proof_of_string_to_upper_ascii_entail_wit_2_2`
  - `proof_of_string_to_upper_ascii_entail_wit_2_3`
  - `proof_of_string_to_upper_ascii_return_wit_1`
- The first obligation is loop-invariant initialization. It should choose `l1 = nil` and `l2 = l`.
- The three `entail_wit_2_*` obligations are loop-preservation branches:
  - lowercase branch after `replace_Znth`
  - below-lowercase branch with no store
  - above-uppercase branch with no store
- The return witness should prove the loop exited at `i = n`, using the preserved nonzero contract fact and the observed current buffer value `0`, then reduce the invariant buffer to the postcondition.
- First attempt: replace each `Admitted.` with the conservative skeleton `pre_process; entailer!.` to identify which obligations are already covered by existing list/array strategies and which need explicit helper lemmas.

## Round 2: first compile failure and proof plan

- `coqc` failed at `proof_of_string_to_upper_ascii_entail_wit_1` with `Attempt to save an incomplete proof`.
- After `pre_process; entailer!`, the remaining goal was the pure fact `Zlength l = n - 0`.
- The missing fact is available from `CharArray.full_length` on `CharArray.full s_pre (n + 1) (l ++ 0 :: nil)`, followed by `Zlength_app_cons`.
- The loop-preservation witnesses also need the same style of explicit list facts:
  - `string_to_upper_ascii_spec` preserves append and length.
  - `upper_ascii_char x` is `x - 97 + 65` in the lowercase branch.
  - `upper_ascii_char x` is `x` in the two non-lowercase branches.
  - the suffix `l2_2` must be destructed into either `nil` or `x :: xs`; the `nil` case contradicts the branch fact that the current character is nonzero.
- Next edit: add local helper lemmas to `proof_manual.v` and replace the five placeholder proofs with explicit prefix/suffix witness scripts.
