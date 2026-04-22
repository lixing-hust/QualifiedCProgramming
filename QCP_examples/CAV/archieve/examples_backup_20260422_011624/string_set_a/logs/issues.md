# Verify Issues

## Parser Compatibility In The Active Annotated Copy

- Phenomenon: the first manual `symexec` run failed immediately with `Unrecognized character: '''` at the annotated postcondition line containing `repeat_Z('a', n)`.
- Trigger: the active annotated file reused the input contract’s character literal syntax, but this verify frontend is parser-fragile around quoted char tokens.
- Localization:
  - failing file: `annotated/verify_20260418_152341_string_set_a.c`
  - failing line: the `Ensure` clause using `repeat_Z('a', n)`
- Fix:
  - kept `input/string_set_a.c` unchanged
  - changed only the active annotated working copy to use the parser-safe integer literal `97`
- Result:
  - `symexec` could parse the annotated program and proceed to real symbolic execution

## Missing Loop Invariant For Prefix Fill

- Phenomenon: before rerunning `symexec`, the active annotated copy had no loop invariant for the `for (i = 0; i < n; ++i)` fill loop.
- Trigger: this function writes an initially undefined buffer progressively, so the verifier needs the written-prefix / undefined-suffix split explicitly.
- Localization:
  - active file: `annotated/verify_20260418_152341_string_set_a.c`
  - loop state that needed preservation:
    - written prefix `CharArray::full(s, i, repeat_Z(97, i))`
    - unwritten suffix `CharArray::undef_seg(s, i, n + 1)`
- Fix:
  - added a loop invariant immediately before the `for` loop
  - recorded the invariant reasoning and initialization/preservation/exit checks in `logs/annotation_reasoning.md`
- Result:
  - rerunning `symexec` succeeded and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`

## Manual Proof Placeholders Needed Concrete Char-Array Lemmas

- Phenomenon: the generated `string_set_a_proof_manual.v` initially contained three `Admitted.` placeholders.
- Trigger: the verify workflow requires all manual lemmas to be completed and forbids leaving `Admitted.` in the final file.
- Localization:
  - file: `output/verify_20260418_152341_string_set_a/coq/generated/string_set_a_proof_manual.v`
  - lemmas:
    - `proof_of_string_set_a_entail_wit_1`
    - `proof_of_string_set_a_entail_wit_2`
    - `proof_of_string_set_a_return_wit_1`
- First failed proof attempt:
  - replacing every placeholder with only `pre_process; entailer!` left `proof_of_string_set_a_entail_wit_1` incomplete
  - the remaining goal was the structural bridge from `CharArray.undef_full` to `CharArray.full ... 0 ... ** CharArray.undef_seg ...`
- Localization process:
  - inspected the post-`entailer!` proof state in `coqtop`
  - compared against `/home/yangfp/QualifiedCProgramming/SeparationLogic/examples/chars_proof_manual.v`
- Fix:
  - `entail_wit_1`: unfolded `repeat_Z`, applied `CharArray.undef_full_to_undef_seg`, then finished with `entailer!`
  - `entail_wit_2`: rewrote with `repeat_Z_tail`, then finished with `entailer!`
  - `return_wit_1`: proved `i = n_pre` by arithmetic, rewrote `CharArray.undef_seg_empty` at `(n_pre + 1)`, then finished with `entailer!`
- Result:
  - `proof_manual.v` compiled without `Admitted.`
  - no new `Axiom` declarations were introduced

## Exit-Suffix Rewrite Needed The `(n_pre + 1)` Index

- Phenomenon: the first attempt to adapt the base `chars_initialize` return proof failed with:
  - `Found no subterm matching "CharArray.undef_seg s_pre n_pre n_pre"`
- Trigger: this function writes the terminating `0` after the loop, so the leftover undefined suffix in the return witness is already at `(n_pre + 1, n_pre + 1)`, not `(n_pre, n_pre)`.
- Localization:
  - file: `output/verify_20260418_152341_string_set_a/coq/generated/string_set_a_proof_manual.v`
  - failing lemma: `proof_of_string_set_a_return_wit_1`
- Fix:
  - changed the empty-suffix rewrite to `CharArray.undef_seg_empty s_pre (n_pre + 1)`
- Result:
  - the full compile chain then passed through `goal_check.v`

## Final Outcome

- `symexec` succeeded on the current annotated file.
- `string_set_a_goal.v`, `string_set_a_proof_auto.v`, `string_set_a_proof_manual.v`, and `string_set_a_goal_check.v` all compiled successfully.
- `string_set_a_proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the successful compile pass.
