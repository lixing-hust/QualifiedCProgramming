## 2026-04-20 manual proof pass 1

After successful `symexec`, `coq/generated/string_remove_char_to_output_proof_manual.v` contains five admitted obligations: invariant initialization (`entail_wit_1`), two loop-preservation branches (`entail_wit_2_1` for `s[i] != c` and `entail_wit_2_2` for `s[i] == c`), the loop-exit assertion (`entail_wit_3`), and the final postcondition after writing the terminator (`return_wit_1`).

The available proof pattern is the existing `string_copy` manual proof: use `pre_process`, split the remaining source/output lists by destructing the suffix when a nonzero read proves `i < n`, and prove loop exit by contradiction from the contract fact that all positions `0 <= k < n` in `l` are nonzero. This task needs additional helper lemmas for `string_remove_char_to_output_spec`: app decomposition, single-element keep/drop cases, and a length upper bound. The final return witness should use `replace_Znth_app_r` at `j = Zlength (string_remove_char_to_output_spec l c)` and choose the postcondition tail directly as the remaining suffix.

## 2026-04-20 manual proof pass 2

First compile failure: `compile_proof_manual.log` stopped at helper lemma `string_remove_char_to_output_spec_zlength_le`, line 65, with `Found no subterm matching "Zlength (? :: ?)" in IHl`. The second branch already has `IHl : 0 <= Zlength (spec l c) <= Zlength l`; the cons length appears in the goal, not in the induction hypothesis. The fix is to remove the bad rewrite in `IHl` and let `lia` combine `rewrite Zlength_cons` in the goal with the unchanged induction hypothesis.

Second compile failure: the same helper lemma still stopped at line 65 with `Cannot find witness`, because a single `rewrite Zlength_cons` did not normalize both cons-length occurrences in the non-equal branch. The next edit changes both inductive branches to `repeat rewrite Zlength_cons` before `lia`.

Third compile failure: Coq stopped in helper `replace_at_prefix_end` with `Cannot infer the implicit parameter A of cons`. The lemma quantified `pre`, `old`, `tail`, and `x` without types, and the open scopes made the `::` type ambiguous. The fix is to type the helper arguments explicitly as `pre tail : list Z` and `old x j : Z`.

Fourth compile failure: `entail_wit_1` had one remaining goal after `entailer!`: `Zlength d = n + 1 - 0`. This is not arithmetic from the pure context; it comes from the output heap predicate `CharArray.full out_pre (n + 1) d`. The fix is to commute the separation conjunction so `prop_apply CharArray.full_length` extracts the output length before choosing the invariant witnesses.

Follow-up on the same witness: `prop_apply` gives `Z.of_nat (length d) = n + 1`, while the remaining goal is phrased as `Zlength d = n + 1 - 0`. After `entailer!`, rewrite `Zlength_correct` and use `lia`.

Fifth compile failure: in `entail_wit_2_1`, `pre_process` substituted the program index `i` with `Zlength l1_2`. The proof still tried to rewrite terms shaped like `n - Zlength l`, but the actual term was `Zlength l1_2 - Zlength l`. The branch proofs need to reason directly with `Zlength l1_2` as the current read index, including the current-head helper and the empty-suffix contradiction.

Correction to pass 5: this witness retains both `i` and the equality `Zlength l1_2 = i`. The failing contradiction term is `i - Zlength l`; using only `Zlength l1_2` does not match. The proof should replace `i - Zlength l` in the terminator contradiction and use `current_head_after_prefix` at index `i` with hypothesis `Zlength l1_2 = i`.

Sixth compile failure: Coq rejected compact destruct syntax `destruct l2_2 as [| x xs]` in this file with an intro-pattern parser error. Existing generated proofs use `destruct l2_2 eqn:...` and then `rename`, so the next edit switches list destructs in the branch witnesses to that form.

Seventh compile failure: after the destruct syntax fix, the empty `l2_2` branch still tried to simplify `Znth (i - Zlength l1_2) (0 :: nil) 0` without first replacing that exact index by `0`. The previous replacement used `Zlength l1_2 - Zlength l1_2`, which does not match. Replace `i - Zlength l1_2` by `0` using `Zlength l1_2 = i`.

Eighth compile failure: unnamed `destruct l2_2 eqn:Hl2` did not introduce the tail as `l0` in this generated context, so the subsequent `rename l0 into xs` failed. Use explicit destruct names with an equation, `destruct l2_2 as [| x xs] eqn:Hl2`, and do the same for `d1_2`.

Correction to pass 8: this Coq/parser context does not accept the compact `as [| x xs]` pattern. Inspecting the generated context shows that unnamed list destruct keeps the original list variable name for the tail in the cons branch. Use `destruct l2_2 eqn:Hl2` and rename `z -> x`, `l2_2 -> xs`; similarly for `d1_2`.

Ninth compile failure: after destructing the source suffix, the script used `H6` for the output suffix length, but `H6` is the source decomposition equality. The output suffix length is `H9 : Zlength d1_2 = n + 1 - j`; use `H9` when destructing `d1_2`.

Tenth compile failure: the cons-branch renames selected the wrong variables. In this context, `destruct l2_2` introduces the head as `z` and the actual tail as `l`, while the old `l2_2` name remains as the equation subject; `destruct d1_2` introduces the actual tail as `l0`. The proof must rename `z -> x`, `l -> xs`, and later `z -> old`, `l0 -> tail`.

Eleventh compile failure: after renaming the source tail `l -> xs`, the subsequent `destruct d1_2` reuses the fresh name `l` for the output tail, not `l0`. Rename that `l` to `tail`.

Twelfth compile failure: in the keep branch, the heap goal still contained `replace_Znth j (Znth i ...) ...`; the proof rewrote `H` and `H0` with the current-head equality but not the goal. Rewrite `Hcur` in all hypotheses and the goal before applying `replace_at_prefix_end`.

Thirteenth compile failure: `entail_wit_2_1` reached `Qed` with an open separation goal. After the output write, the antecedent heap is ordered as `CharArray.full out ** CharArray.full s`, but the invariant conclusion is `CharArray.full s ** CharArray.full out`. Commute the sepcon after rewriting the output list and before selecting witnesses.

Fourteenth compile failure: `entail_wit_2_1` still reached `Qed` with an open goal, but the loose `try (rewrite ...; reflexivity)` chain hid which generated side condition remained. The next edit applies all expected normalizations (`keep_single`, `Zlength_app_cons`, `Zlength_cons`, append associativity, `simpl`) uniformly to all `entailer!` subgoals before trying `lia`/`reflexivity`.

Fifteenth compile failure: `entail_wit_2_1` is solved; `entail_wit_2_2` now reaches `Qed` with an open side condition. Apply the same uniform cleanup style to the drop branch, using `string_remove_char_to_output_spec_drop_single`, `Zlength_app_cons`, append associativity, `simpl`, `lia`, and `reflexivity`.

Sixteenth compile failure: in `entail_wit_3`, `rewrite H3` inside the `list_eq_ext` pointwise proof triggered setoid-rewrite evars. The goal only needs replacing the right-hand list `l` with `l1 ++ l2`; use `replace l with (l1 ++ l2) by exact H3`, then `app_Znth1`.

Seventeenth compile failure: after `pre_process`, the decomposition equality in `entail_wit_3` is `H5 : l = l1 ++ l2`, not `H3`. Use `H5` in the explicit replacement.

Eighteenth compile failure: the explicit `replace l with (l1 ++ l2)` requires a proof of `(l1 ++ l2) = l`, while `H5` is oriented as `l = l1 ++ l2`. Use `by (symmetry; exact H5)`.

Nineteenth compile failure: the parser rejected `destruct d1 as [| x t]` in `entail_wit_3`. Use unnamed destruct, rename `z -> x` and `l -> t`, and use `H8` as the output suffix length fact.

Twentieth compile failure: `entail_wit_3` still had an open goal after splitting `d1`; the remaining shape is the append normalization between `spec ++ x :: t` and `(spec ++ x :: nil) ++ t`. Add `rewrite <- app_assoc` plus `simpl` to the witness cleanup.

Twenty-first compile failure: the generic cleanup still leaves the exit heap shape unresolved. Normalize the antecedent output list before `Exists`: prove `spec l c ++ x :: t = (spec l c ++ x :: nil) ++ t` by append associativity and rewrite it before calling `entailer!`.

Twenty-second compile failure: in `entail_wit_3`, the original input list `l` is still in scope when destructing `d1`, so the destructor names the output tail `l0`. Renaming `l -> t` removed the original input list. Rename `l0 -> t` instead.

Correction to pass 22: in this generated context the tail after `destruct d1` reuses the original name `d1`, not `l0`. Rename `d1 -> t`.

Twenty-third compile failure: inserting a temporary `Show` at the end of `entail_wit_3` printed `No more goals`, but `Qed` still reported an incomplete proof. This indicates shelved obligations from existential/separation automation rather than focused goals. Remove `Show` and add an `Unshelve` cleanup with `lia`/`reflexivity` fallbacks.

Twenty-fourth compile failure: `Qed` still reports an incomplete proof after the cons branch has no focused goals, so a leftover destruct branch is likely unfocused. Add a final `all:` cleanup for the nil-length contradiction before `Qed`.

Twenty-fifth compile failure: the proof still reports incomplete with no visible focused goal. Broaden the `Unshelve` cleanup to provide default list and integer witnesses for any shelved evars before closing with `lia`/`reflexivity`.

Twenty-sixth proof change: the incomplete `entail_wit_3` state appears tied to the `list_eq_ext` proof used to reconstruct `l1 = l`. Replace that proof strategy. At loop exit, `Zlength l1 = n`, `Zlength l = n`, and `l = l1 ++ l2`; therefore `Zlength l2 = 0`, so `l2 = nil`, and then `l = l1` follows by `app_nil_r`. This is simpler and avoids extensional equality machinery.

Twenty-seventh compile failure: in the proof that `l2 = nil`, the nonempty branch tried to rewrite `Zlength_cons` in the equality goal itself. That branch should be discharged by contradiction from lengths. Use `exfalso`, rewrite `Zlength_app` and `Zlength_cons` in `H12`, and finish with `lia`.

Twenty-eighth compile failure: `H12` is still phrased as `Zlength l = n`, so `Zlength_app` does not match until the decomposition equality `H5 : l = l1 ++ l2` is rewritten into `H12`. Rewrite `H5` in `H12` before `Zlength_app`.

Twenty-ninth proof cleanup: temporary `Show`/`Show Existentials` showed no focused goals or printed evars, but `Qed` still reported incomplete. Try the older `Grab Existential Variables` cleanup form after the branch proof, with default list/integer witnesses and pure closers.

## 2026-04-20 retry proof pass 1

`coqtop` on `proof_of_string_remove_char_to_output_entail_wit_3` showed that the previous script did not have a visible list/existential goal left; the remaining focused goal after `entailer!` was the separation entailment `&( "i") # Int |-> Zlength l1 |-- &( "i") # Int |-> n`. The proof already established `Hi_eq_n : Zlength l1 = n` after loop exit and `l2 = nil`, but it did not rewrite the heap cell before choosing witnesses. The next edit rewrites `Hi_eq_n` immediately after substituting `l = l1`, before destructing the output suffix, so the stack cell shape matches the loop-exit assertion directly.

## 2026-04-20 retry proof pass 2

After rewriting `Hi_eq_n`, `proof_manual.v` passed `entail_wit_3` and moved to `proof_of_string_remove_char_to_output_return_wit_1`. The new compile error at line 260 was `Found no subterm matching "replace_Znth j 0 (string_remove_char_to_output_spec l c_pre ++ x :: t_2)" in the current goal.` The return witness heap still uses the generated nested shape `replace_Znth j 0 ((string_remove_char_to_output_spec l c_pre ++ x :: nil) ++ t_2)`. The next edit changes the local replacement lemma instance to that nested shape, proving it by first normalizing with `rewrite <- app_assoc; simpl` and then applying `replace_at_prefix_end`.

## 2026-04-20 retry proof pass 3

The nested return replacement matched the generated antecedent, but direct `apply replace_at_prefix_end` still failed because that helper concludes the flattened RHS `spec ++ 0 :: t_2` while the generated postcondition expects `(spec ++ 0 :: nil) ++ t_2`. The next edit rewrites with `replace_at_prefix_end` after normalizing the antecedent, then reassociates the RHS with `rewrite <- app_assoc; reflexivity`.
