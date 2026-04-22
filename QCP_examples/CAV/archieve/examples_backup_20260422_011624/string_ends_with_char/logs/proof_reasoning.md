## Iteration 1: generated manual obligations after successful symexec

Fresh `symexec` generated seven manual obligations in `coq/generated/string_ends_with_char_proof_manual.v`:

- `proof_of_string_ends_with_char_safety_wit_6`: prove `i + 1` is inside signed-int range from `0 <= i`, `i < n`, and `n < INT_MAX`-style facts carried by the loop context.
- `proof_of_string_ends_with_char_safety_wit_9`: same signed-int range obligation for `i + 1` on the non-sentinel branch.
- `proof_of_string_ends_with_char_entail_wit_1`: prove the fall-through from `s[0] != 0` implies `0 < n`; this uses the contract fact that all positions below `n` are nonzero and the sentinel is at index `n`.
- `proof_of_string_ends_with_char_entail_wit_3`: prove loop preservation after increment, especially `(i + 1) < n` from the observed nonzero value at `s[i + 1]`.
- `proof_of_string_ends_with_char_entail_wit_4`: prove loop exit gives `i = n - 1` from `s[i + 1] == 0`.
- `proof_of_string_ends_with_char_return_wit_1`: prove the empty-string return matches the `n == 0` postcondition case.
- `proof_of_string_ends_with_char_return_wit_3`: prove the final false branch matches the `l[n - 1] != c` postcondition case.

The first proof attempt will replace the generated `Admitted.` placeholders with the standard skeleton `pre_process; entailer!.` and then compile. I expect the safety witnesses may close directly, while the string sentinel obligations may need explicit `Znth_app1` / `Znth_app2` style list reasoning or a small helper about the unique zero terminator in `app l (cons 0 nil)`.

## Iteration 2: invariant bound issue moved back to annotation

First compile failure after the proof skeleton was in `proof_of_string_ends_with_char_safety_wit_6`: `coqc` reported an incomplete proof. Inspecting the proof state after `pre_process; entailer!` showed the remaining pure goal `i + 1 <= 2147483647`, with assumptions `0 <= i`, `i < n`, and `0 < n`, but no `n < INT_MAX`. Since this is state from the original precondition that the loop must preserve, I moved the fix to the annotated C by adding `n < INT_MAX` to the pre-loop assertion, loop invariant, and loop-exit assertion, then reran `symexec`.

After regeneration, `safety_wit_6` and `safety_wit_9` moved to `proof_auto.v`; the manual file now has five obligations: `entail_wit_1`, `entail_wit_3`, `entail_wit_4`, `return_wit_1`, and `return_wit_3`.

## Iteration 3: sentinel uniqueness proof pattern

The next compile failure was `proof_of_string_ends_with_char_entail_wit_1`, again as an incomplete proof. The direct proof state after `pre_process; entailer!` had to prove `0 < n` from `Znth 0 (l ++ 0 :: nil) 0 <> 0`, `0 <= n`, and the nonzero-prefix property, but the length connection between `l` and `n` was still hidden inside `CharArray.full`.

Reusable pattern found in `examples/string_length/coq/generated/string_length_proof_manual.v` and `examples/string_contains_char/coq/generated/string_contains_char_proof_manual.v`: call `prop_apply CharArray.full_length; Intros`, derive `Zlength l = n` from the resulting length of `l ++ 0 :: nil`, and then use `app_Znth1` / `app_Znth2` with arithmetic side conditions to distinguish prefix positions from the terminator. I will use that pattern for:

- `entail_wit_1`: if `n = 0`, index 0 is the terminator, contradicting the observed nonzero read.
- `entail_wit_3`: if `i + 1 >= n`, then since `i < n`, index `i + 1` is exactly `n`, so the observed nonzero read contradicts the terminator.
- `entail_wit_4`: if `i + 1 < n`, the nonzero-prefix property contradicts the observed zero read; therefore `i + 1 = n`.
- `return_wit_1`: the early zero at index 0 forces `n = 0`, selecting the empty-string postcondition case.
- `return_wit_3`: with `i = n - 1`, rewrite the final read through `app_Znth1` to select the `l[n - 1] != c` postcondition case.

## Iteration 4: final disjunction selection and compile success

After implementing the `CharArray.full_length` / `Zlength_app_cons` pattern, `coqc` first failed in `return_wit_1` because the proof tried to use lowercase `right; right` on a separation-logic `orp` goal. This goal is not Coq's inductive `or`; the stable local pattern is to rewrite with `derivable1_orp_intros1` or `derivable1_orp_intros2`.

For `return_wit_1`, the empty-string branch is the third postcondition case. The target is parsed as `(case1 || case2) || case3`, so one `rewrite <- derivable1_orp_intros2` selects the third case. For `return_wit_3`, the false final comparison is the first postcondition case, so two `rewrite <- derivable1_orp_intros1` steps select the first case inside the nested disjunction. After those changes, `string_ends_with_char_proof_manual.v` compiled successfully.

The full documented replay then compiled `string_ends_with_char_goal.v`, `string_ends_with_char_proof_auto.v`, `string_ends_with_char_proof_manual.v`, and `string_ends_with_char_goal_check.v`. A final grep found no `Admitted.` in `proof_manual.v` and no user-added top-level `Axiom`; the only `Axioms` text is the standard imported module name in the generated header.
