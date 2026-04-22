# Proof Reasoning

## Iteration 1: generated obligations after successful symexec

- Current generated manual lemmas:
  - `proof_of_string_set_a_entail_wit_1`
  - `proof_of_string_set_a_entail_wit_2`
  - `proof_of_string_set_a_return_wit_1`
- First compile probe of `goal.v`, `proof_auto.v`, and `proof_manual.v` succeeded only because the generated file still used `Admitted.`.
- Shape diagnosis:
  - `entail_wit_1` is the loop-entry framing step from `undef_full` to `full 0 (...) * undef_seg 0 (...)`
  - `entail_wit_2` is the loop-preservation normalization from `app(repeat_Z 97 i, [97])` to `repeat_Z 97 (i + 1)`
  - `return_wit_1` is the exit framing step after writing `0` into the final slot
- Initial hypothesis: these are all lightweight witness obligations where `pre_process` and `entailer!` should discharge the separation-logic framing and the trivial equalities, because the loop invariant already carries the right prefix/suffix shape.
- Next action: replace the three `Admitted.` placeholders with minimal proofs and recompile to discover the first real failure, if any.

## Iteration 2: `entail_wit_1` still needed explicit char-array normalization

- First stable compile failure:
  - file: `output/verify_20260418_152341_string_set_a/coq/generated/string_set_a_proof_manual.v`
  - lemma: `proof_of_string_set_a_entail_wit_1`
  - error: `Attempt to save an incomplete proof`
- `coqtop` inspection after `pre_process; entailer!` showed the remaining goal was:
  - `CharArray.undef_full s_pre (n_pre + 1) |-- CharArray.full s_pre 0 (repeat_Z 97 0) ** CharArray.undef_seg s_pre 0 (n_pre + 1)`
- Diagnosis: this is the same initialization obligation as the repository’s base `chars_initialize` example; it does not close automatically until the empty-prefix list and the `undef_full -> undef_seg` bridge are made explicit.
- Reusable pattern found:
  - `/home/yangfp/QualifiedCProgramming/SeparationLogic/examples/chars_proof_manual.v`
  - `entail_wit_1`: unfold `repeat_Z`, then `sep_apply CharArray.undef_full_to_undef_seg`
  - `entail_wit_2`: `rewrite repeat_Z_tail`
  - `return_wit_1`: derive `i = n_pre`, then rewrite `CharArray.undef_seg_empty`
- Next action: adapt that exact proof pattern to `string_set_a_proof_manual.v` and rerun the full compile chain.

## Iteration 3: exit suffix index was off by one

- New compile failure:
  - file: `output/verify_20260418_152341_string_set_a/coq/generated/string_set_a_proof_manual.v`
  - lemma: `proof_of_string_set_a_return_wit_1`
  - error: `Found no subterm matching "CharArray.undef_seg s_pre n_pre n_pre"`
- Diagnosis: unlike plain `chars_initialize`, this function writes the trailing `0` after the fill loop, so the return witness already contains `CharArray.full ... (i + 1)` and the leftover undefined suffix is `CharArray.undef_seg s_pre (n_pre + 1) (n_pre + 1)` once `i = n_pre`.
- Fix direction: keep the same proof shape, but rewrite `CharArray.undef_seg_empty` at `(n_pre + 1)` instead of `n_pre`.
