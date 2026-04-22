## 2026-04-20 proof plan

Fresh symbolic execution generated four manual obligations in `coq/generated/array_replace_negative_zero_proof_manual.v`: `proof_of_array_replace_negative_zero_entail_wit_1`, `proof_of_array_replace_negative_zero_entail_wit_2_1`, `proof_of_array_replace_negative_zero_entail_wit_2_2`, and `proof_of_array_replace_negative_zero_return_wit_1`. The first is loop-invariant initialization. The middle two are loop preservation for the negative and nonnegative branches. The last is the function postcondition after loop exit.

The generated goals are pure list/array-shape witnesses over `IntArray.full`. The proof pattern matches the existing `array_replace_k` workspace: reconstruct the unprocessed suffix as `sublist i n_pre l`, choose the next invariant state with prefix `l1_2 ++ cons new_value nil` and suffix `sublist (i + 1) n_pre l`, rewrite the heap list using `replace_Znth_app_r` or `sublist_split`, and use the invariant prefix property for indices below `i`. For the new index `i`, the negative branch uses the guard plus the suffix invariant to derive `Znth i l 0 < 0`; the nonnegative branch uses the guard to derive `Znth i l 0 >= 0`.

The return witness should first prove `i_2 = n_pre` from loop exit and invariant bounds, prove `l2 = nil` from its zero length, rewrite `app l1 nil`, and choose `l1` as the final `l0`.

## 2026-04-20 first compile failure

The first full compile replay compiled `array_replace_negative_zero_goal.v` and `array_replace_negative_zero_proof_auto.v`, then failed in `array_replace_negative_zero_proof_manual.v` at line 125 with `Error: Tactic failure: Cannot find witness.` The failing command was the negative-branch rewrite `rewrite (sublist_split i n_pre (i + 1) l) by lia` inside the replacement-list equality. This is a length side-condition issue: the context has `n_pre = Zlength l` / `Zlength l = n_pre`, but the local rewrite is more stable when it explicitly adds `pose proof (Zlength_correct l)` before `lia`, matching other generated array proofs. I will apply the same explicit side-condition proof in both branch rewrites.

## 2026-04-20 second compile failure

After making the `sublist_split` side condition explicit, `coqc` next failed at line 135 with `Found no subterm matching "Zlength (?M9392 ++ ?M9393)" in the current goal.` The local script had already executed `rewrite Zlength_correct in *`, so the generated length side goal may be normalized to `length`/`Z.of_nat` form before the bullet runs. The fix is to make the length bullets tolerant of either form: try `Zlength_app`, then try `Zlength_correct` and `length_app`, and finish with `lia`.

## 2026-04-20 third compile failure

The tolerant length bullet still failed with `Cannot find witness`, and a `coqtop` probe showed that the broad `rewrite Zlength_correct in *` was converting useful `Zlength` hypotheses into `Z.of_nat (length ...)`, while the generated goal still contains `Zlength` facts to be solved by standard list lemmas. The better fix is to avoid that broad normalization before `entailer!` in both loop-preservation proofs and keep the branch scripts in the same `Zlength` style as `array_replace_k`.

## 2026-04-20 fourth compile failure

After removing broad `Zlength` normalization, the same line reported no `Zlength` app subterm because it was not yet the length side condition. The generated entailment first asks for the explicit branch fact at the original list index: `Znth i l 0 < 0` in the negative branch and `Znth i l 0 >= 0` in the nonnegative branch. Both facts were already derived as `Hli_neg` and `Hli_ge`, so the proof needs one leading bullet using those facts before the length bullets.

## 2026-04-20 fifth compile failure

The next compile showed the actual first post-`entailer!` goal in the negative branch is the suffix preservation fact:
`forall t_2, 0 <= t_2 < n_pre - (i + 1) -> Znth t_2 (sublist (i + 1) n_pre l) 0 = Znth (i + 1 + t_2) l 0`.
The previous script had this proof as the final bullet. I will move that suffix bullet to the front in both preservation proofs and leave the prefix proof to use `Hli_neg` / `Hli_ge` in the `k = i` case.

## 2026-04-20 sixth compile failure

The suffix bullet then failed at `apply Znth_indep` because the two sides had mathematically equal but syntactically different indices, `k + (i + 1)` and `i + 1 + k`. This is not an independence/default-value issue; it is only arithmetic normalization. The fix is to replace `k + (i + 1)` with `i + 1 + k` by `lia` and finish by reflexivity.

## 2026-04-20 seventh compile failure

After fixing suffix arithmetic, `coqc` reported that the next bullet again had no `Zlength (_ ++ _)` subterm. That means the next goal after suffix preservation is the suffix `Zlength (sublist ...)` fact, not the prefix append length. I will swap the two length bullets so `Zlength_sublist0` runs before `Zlength_app`.

## 2026-04-20 eighth compile failure

The swapped suffix-length bullet failed with `Unable to unify "list ?A" with "Z"` at `apply Zlength_sublist0`. In this environment, the stable form is not applying `Zlength_sublist0` directly but rewriting with `Zlength_sublist` under the current bounds and then using `lia`. I will replace both suffix-length bullets with `rewrite Zlength_sublist by lia; lia`.

## 2026-04-20 ninth compile failure

After switching to `Zlength_sublist`, the next failure said there was no `Zlength (sublist ...)` subterm. The remaining pure side conditions are being reordered by `entailer!`; one may be a direct arithmetic fact, the append length, or the sublist length. I will make the two pure-length bullets generic by trying both `Zlength_app` and `Zlength_sublist`, simplifying, and closing with `lia`.

## 2026-04-20 tenth compile failure

The generic positional length bullet still failed with `Cannot find witness`, which indicates the post-`entailer!` goal order is not stable enough for fixed bullets. The remaining goals are all distinguishable by shape: suffix pointwise equality, append length, sublist length, and prefix pointwise relation. I will replace positional bullets in both preservation proofs with unordered `all: try solve [...]` clauses so each side condition is solved by the tactic matching its goal shape.

## 2026-04-20 eleventh compile failure

The unordered prefix tactic initially used bullet markers inside `try solve [...]`, and Coq rejected that with `Syntax error: '|' or ']' expected`. The proof logic is unchanged, but it must be written with bracketed branches inside the tactic expression instead of bullets.

## 2026-04-20 twelfth compile failure

The bracketed prefix tactic then failed in the `match goal` pattern with `The reference i was not found in the current environment`. The tactic was being tried against goals whose local context did not match that exact binder name. In the actual preservation goals, the generated prefix invariant is hypothesis `H6`, so I will use `pose proof (H6 k ltac:(lia))` directly instead of matching on the hypothesis shape with a hard-coded `i`.

## 2026-04-20 thirteenth compile failure

After removing the hard-coded match, `entail_wit_2_1` reached `Qed` with an incomplete proof. The shape-specific tactics no longer fail, but one residual goal is not matched. Since the branch proof has already rewritten the heap list to the chosen invariant list, the remaining residual should be either plain arithmetic or a direct separation entailment. I will add final fallback clauses `all: try solve [lia]` and `all: try solve [entailer!]` after the shape-specific solvers in both branch proofs.

## 2026-04-20 fourteenth compile failure

The `Show` probe after the fallbacks showed exactly two residual goals in `entail_wit_2_1`: the processed-prefix pointwise relation and the prefix append length. The generic prefix solver did not consume the pointwise relation, and the append-length solver was left behind. I will add two explicit final bullets after the generic solvers: first the prefix relation proof by splitting `t < i` versus `t = i`, then `rewrite Zlength_app; simpl; lia`.

## 2026-04-20 fifteenth compile failure

The explicit prefix proof then failed in an `app_Znth1` side condition because the side goal was already reduced and no longer contained a `Zlength (_ ++ _)` subterm. I will make the side-condition proofs use `try rewrite Zlength_app; simpl; lia` instead of forcing the rewrite.

## 2026-04-20 final proof success

The remaining failures were localized to generated side goals after simplification. For the branch prefix lengths, Coq had already reduced the append length to `Zlength l1_2 + Zlength (_ :: nil)`, so the proof now rewrites `Zlength_cons` and `Zlength_nil` directly. The return proof uses `Zlength_nil_inv` to discharge the empty suffix after `i = n` and then applies the processed-prefix invariant hypothesis to prove the postcondition. The final manual proof compiles with no `Admitted.` and no new `Axiom`.
