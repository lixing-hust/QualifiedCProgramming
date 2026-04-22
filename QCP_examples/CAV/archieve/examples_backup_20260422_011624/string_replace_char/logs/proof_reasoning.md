# Proof Reasoning

## Round 1: generated obligations after successful symexec

- Current generated manual file: `output/verify_20260420_034132_string_replace_char/coq/generated/string_replace_char_proof_manual.v`.
- `symexec` generated four manual obligations: `proof_of_string_replace_char_entail_wit_1`, `proof_of_string_replace_char_entail_wit_2_1`, `proof_of_string_replace_char_entail_wit_2_2`, and `proof_of_string_replace_char_return_wit_1`.
- The shape matches the verified `string_to_upper_ascii` in-place string update pattern: initialization chooses `l1 = nil, l2 = l`; each nonzero loop iteration splits `l2` into `x :: xs`; the old-character branch proves that `replace_Znth i new_c` converts the current head into the next transformed prefix; the other branch proves the current head is preserved because `replace_char x old_c new_c = x`; the return witness first proves `i = n` using the contract fact that all original `l[0..n)` elements are nonzero.
- Existing generated script is only `Proof. Admitted.` for all four obligations, so the next edit will add local helper lemmas for:
  - `string_replace_char_spec` distribution over append
  - preservation of `Zlength`
  - identifying the current unprocessed head after the transformed prefix
  - rewriting the assignment branch into the next invariant heap list
  - preserving the nonmatching branch list
- No annotation change is planned because the witness has all necessary facts: the invariant preserved `old_c`, `new_c`, `l == l1 ++ l2`, `Zlength` bounds, the nonzero-input fact, and the heap list shape.

## Round 2: first compile failure in helper lemma

- First full compile attempt stopped in `coq/generated/string_replace_char_proof_manual.v` at line 37 inside `string_replace_char_spec_zlength`.
- Error text from `logs/compile_proof_manual.log`: `Tactic failure:  Cannot find witness.`
- The failure is not about a generated VC; it occurs before any witness proof. The step used `rewrite !Zlength_cons; lia`, but the arithmetic automation did not use the induction hypothesis robustly after the recursive spec call.
- Next edit: replace that final `lia` with an explicit rewrite by the induction hypothesis, making the length-preservation proof structural rather than automation-dependent.

## Round 3: `entail_wit_1` solved before copied cleanup

- Second compile attempt reached `proof_of_string_replace_char_entail_wit_1` and failed at line 126 with `Error: No such goal.`
- The proof state was already closed by `entailer!` after choosing `l1 = nil` and `l2 = l`; the remaining copied `Zlength_correct` and `Zlength_app_cons` cleanup had no goal to operate on.
- Next edit: remove the dead cleanup lines and keep `entailer!` as the complete proof for this initialization witness.

## Round 4: generated hypothesis numbering mismatch

- Third compile attempt reached `proof_of_string_replace_char_entail_wit_2_1` and failed at line 133: `Found no subterm matching "?M6287 ++ nil" in H2.`
- The script was copied from the closest example, but this generated witness has an extra leading pure fact `0 <= n + 1`, so the hypothesis numbers differ. In this proof, `H4` is `l = app l1_2 l2_2`, `H6` is `Zlength l1_2 = i`, and `H7` is `Zlength l2_2 = n - i`; `H2` is only the bound `0 <= i`.
- Next edit: adjust the indices in both loop-step witnesses and in the return witness to match the current generated goal.

## Round 5: nil-suffix branch append normalization

- Fourth compile attempt still failed in `proof_of_string_replace_char_entail_wit_2_1`, now at the `app_Znth2` rewrite for the nil-suffix contradiction.
- Error text: `Found no subterm matching "Zlength (string_replace_char_spec ?M6298 ?M6299 ?M6300)" in the current goal.`
- Cause: after `destruct l2_2`, the expression still contained an `++ nil` layer, so the `app_Znth2` rewrite side condition did not expose the expected `Zlength (string_replace_char_spec ...)` subterm.
- Next edit: rewrite `app_nil_r` in the branch facts first, then prove the contradiction from the direct `Znth ... <> 0` fact.

## Final proof result

- After the append-normalization fix, the full compile replay succeeded for `original/string_replace_char.v`, `string_replace_char_goal.v`, `string_replace_char_proof_auto.v`, `string_replace_char_proof_manual.v`, and `string_replace_char_goal_check.v`.
- `string_replace_char_proof_manual.v` has no remaining `Admitted.` proof and no top-level `Axiom` declaration.
- No further annotation or contract changes were needed.
