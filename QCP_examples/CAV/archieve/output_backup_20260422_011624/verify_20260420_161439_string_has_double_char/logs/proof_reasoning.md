# Proof Reasoning

## Round 1

- After the final clean `symexec` run, `coq/generated/string_has_double_char_proof_manual.v` contains five admitted obligations: `proof_of_string_has_double_char_entail_wit_2`, `proof_of_string_has_double_char_entail_wit_3`, `proof_of_string_has_double_char_return_wit_1`, `proof_of_string_has_double_char_return_wit_2`, and `proof_of_string_has_double_char_return_wit_3`.
- `entail_wit_2` is the bridge after `s[i] != 0`; the missing fact is `i + 1 <= n`, which follows because if `i == n` then `Znth i (l ++ 0 :: nil) 0` is the terminator, contradicting the branch condition. The proof will use `CharArray.full_length` to derive `Zlength l = n`.
- `entail_wit_3` is loop preservation after the unequal adjacent pair and `i++`; the main semantic step is proving the processed-prefix property for every `j < i + 1`, splitting on whether `j < i` or `j == i`.
- `return_wit_1` returns `1` after finding equal adjacent characters. The branch condition gives equality on `l ++ 0 :: nil`, and the fact `Znth (i + 1) ... <> 0` plus the nonzero-prefix contract should force `i + 1 < n`, allowing the current `i` as the existential witness.
- `return_wit_2` exits after `s[i + 1] == 0`; the nonzero-prefix contract should force `i + 1 == n`, making every valid adjacent pair have left index `< i`, so the invariant gives the universal postcondition.
- `return_wit_3` exits after `s[i] == 0`; the nonzero-prefix contract should force `i == n`, making the same universal postcondition available from the invariant.
- The closest reusable patterns are `examples/array_has_adjacent_equal/coq/generated/array_has_adjacent_equal_proof_manual.v` for the final universal return shape and `examples/string_contains_char/coq/generated/string_contains_char_proof_manual.v` for deriving `Zlength l = n` and forcing an index to equal `n` from the terminator and the nonzero-prefix contract.

## Round 2

- First compile probe of `proof_manual.v` failed at line 56 in `proof_of_string_has_double_char_entail_wit_3`.
- Error: Coq tried to apply hypothesis `H4 : n < 2147483647` to the goal `Znth j l 0 <> Znth (j + 1) l 0`.
- Cause: the script relied on an unstable generated hypothesis name for the processed-prefix invariant; in the actual proof state that invariant was named `H6`, not `H4`.
- Fix direction: replace the fragile `apply H4` with a `match goal` that selects the hypothesis by its type shape `forall j, ... -> Znth j l 0 <> Znth (j + 1) l 0`.

## Round 3

- Second compile probe failed at line 63 in `proof_of_string_has_double_char_entail_wit_3` with `Tactic failure: Cannot find witness` while rewriting `Znth i (l ++ 0 :: nil)` using `app_Znth1`.
- Cause: the proof had not derived `Zlength l = n` or `i + 1 < n` before the rewrite. The branch hypothesis only gave `Znth (i + 1) (l ++ 0 :: nil) 0 <> 0` and `i + 1 <= n`; if `i + 1 == n`, that position is the terminator, contradiction.
- Fix direction: before `entailer!`, use `CharArray.full_length` to derive `Zlength l = n`, then prove `i + 1 < n` from the nonzero branch condition. This supplies the explicit bounds needed by `app_Znth1`.

## Round 4

- Third compile probe progressed through `entail_wit_3` and failed at line 116 in `proof_of_string_has_double_char_return_wit_1`.
- Error: after `pre_process`, using `right; Exists i_3` on the separating-logic disjunction produced a model-level type mismatch involving `derivable1s_exp_r`.
- Cause: this return witness is closer to the completed adjacent-equality example, which proves disjunctive postconditions with `intros; Intros; right/left; Exists ...; entailer!`. The earlier script mixed that shape with `pre_process`, leaving the goal in a form where ordinary Coq `right` was not the right introduction tactic.
- Fix direction: rewrite the three return witnesses to use the direct `intros; Intros` style, derive `CharArray.full_length` there, then introduce the desired postcondition branch.

## Round 5

- The next compile probe passed `return_wit_1` after switching the existential introduction to model-level `exists` and explicitly unfolding the postcondition conjunction.
- It then failed in `return_wit_2` at the assertion that `Znth (i_3 + 1) l 0 <> 0`.
- Error: Coq attempted to use `H3 : n < 2147483647` as the nonzero-prefix hypothesis.
- Cause: the proof again relied on a generated hypothesis name that changed under the direct `intros; Intros` proof shape.
- Fix direction: select the nonzero-prefix fact by type shape instead of by the name `H3`.

## Round 6

- After fixing the nonzero-prefix lookup, `return_wit_2` reached the left postcondition branch but `entailer!` left a model-level conjunction goal; attempting `intros` produced `No product even after head-reduction`.
- `coqtop` showed the remaining goal shape was `([|0 = 0|] && ([|forall ...|] && CharArray.full ...)) m`.
- Fix direction: after selecting `left`, unfold `andp` and `coq_prop`, simplify, split the model-level conjunction explicitly, and prove the universal adjacent-inequality fact using the processed-prefix invariant plus `i_3 + 1 = n`.
