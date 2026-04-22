## 2026-04-21 proof start after semantic-prefix symexec

Fresh generated `merge_sorted_arrays_proof_manual.v` contains six admitted manual obligations: `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_4`, `entail_wit_6`, and `return_wit_1`. The current invariant now carries both the output memory shape `app(lout_done, sublist(k, n + m, lo))` and the semantic fact `lout_done = merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb))`.

Initial proof plan: try the standard generated-VC pattern first. For initialization choose `nil` as the written prefix. For each write-preservation witness choose the old prefix extended by the value just written, e.g. `lout_done_2 ++ Znth i la 0 :: nil` or `lout_done_2 ++ Znth j lb 0 :: nil`. Then run `entailer!`; if this fails, inspect the first concrete Coq error and decide whether helper lemmas are needed for `replace_Znth`, `sublist`, and the recursive merge spec.

## 2026-04-21 proof failure: first skeleton leaves open goals

First compile failure after replacing `Admitted.` with standard witnesses: `coqc` failed at `merge_sorted_arrays_proof_manual.v:27:0-4` in `proof_of_merge_sorted_arrays_entail_wit_1` with `Attempt to save an incomplete proof`. This means `Exists nil; entailer!` did not prove all pure/list side conditions for loop initialization. Next step is to inspect the post-`entailer!` proof state for that theorem and add only the missing list rewrites or helper lemmas.


## 2026-04-21 retry proof patch

The current blocker is `proof_of_merge_sorted_arrays_entail_wit_1`: after `Exists nil; entailer!`, the remaining goal is the heap entailment `IntArray.full out_pre (n_pre + m_pre) lo |-- IntArray.full out_pre (n_pre + m_pre) (nil ++ sublist 0 (n_pre + m_pre) lo)`. The available fact `H4 : Zlength lo = n_pre + m_pre` is enough; the proof needs an explicit `sublist_self` rewrite before `entailer!`. Next I will patch only this theorem first, compile, then inspect the next concrete witness failure.

## 2026-04-21 proof status after strict invariant

After the strict tie-order invariant, `symexec` succeeds again and the generated VCs are semantically correct. A `coqtop` probe of `entail_wit_2_1` after the standard witness leaves five goals: output-array `replace_Znth` normalization, the merge-prefix semantic equality, prefix length, and two cross-boundary preservation facts. The preservation facts are direct from the new invariant plus sortedness/branch condition; the heap goal is a standard `replace_Znth_app_r`/`sublist_split` rewrite. The real remaining proof work is reusable helper lemmas for `merge_sorted_arrays_spec` stating that appending the current `a` value or current `b` value to the appropriate prefix matches the spec under the cross-boundary ordering facts and the spec tie rule. I am replacing generated `Admitted.` placeholders with proof skeletons and leaving the first concrete blocker at those helper lemmas rather than bypassing proofs.

## 2026-04-21 retry proof helper patch

Current compile replay stops at `proof_of_merge_sorted_arrays_entail_wit_2_1` with five remaining goals after `Exists (lout_done_2 ++ Znth i_3 la 0 :: nil); entailer!`: the output heap list after `replace_Znth`, the semantic prefix equality for `merge_sorted_arrays_spec`, the prefix length, and the two cross-boundary ordering facts. The available hypotheses are the old semantic equality `lout_done_2 = merge_sorted_arrays_spec (sublist 0 i_3 la) (sublist 0 j_3 lb)`, the sortedness of `la`/`lb`, and the cross-boundary facts. The current script is insufficient because `entailer!` does not reason through the recursive merge spec or through the append-at-end shape of `replace_Znth`. Next patch: add local helper lemmas for `merge_sorted_arrays_spec` when appending a largest final `a` or `b` element, a helper that turns `In (sublist ...)` into a bounded `Znth`, and a helper that rewrites the output write from `replace_Znth k x (prefix ++ suffix)` to `(prefix ++ [x]) ++ suffix`. Then use those helpers in the first failing witness and iterate to the next concrete compile failure.

## 2026-04-21 proof progress: first merge branch closed

After adding the local merge-spec append and output-write normalization helpers, `proof_of_merge_sorted_arrays_entail_wit_2_1` compiles. The next compile replay stops at `proof_of_merge_sorted_arrays_entail_wit_2_2` with the same shape for the branch that writes `b[j_3]`: normalize `replace_Znth`, prove `merge_sorted_arrays_spec (sublist 0 i_3 la) (sublist 0 (j_3+1) lb)` equals the old merged prefix plus `Znth j_3 lb 0`, and preserve cross-boundary facts. The needed facts are `Znth i_3 la 0 > Znth j_3 lb 0`, sortedness of `lb` for old consumed b values, sortedness of `la` for future a values, and the old cross-boundary invariant for consumed a values. Next patch mirrors the first branch using `merge_sorted_arrays_spec_app_b_last`.

## 2026-04-21 manual continuation: helper lemma shape

The current generated Coq files were regenerated with `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`; `symexec` completed successfully and produced fresh `merge_sorted_arrays_goal.v`, `merge_sorted_arrays_proof_auto.v`, `merge_sorted_arrays_proof_manual.v`, and `merge_sorted_arrays_goal_check.v`.

The first real proof split is `proof_of_merge_sorted_arrays_entail_wit_2_1`. A `coqtop` probe after `pre_process; Exists (lout_done_2 ++ [Znth i_3 la 0]); entailer!.` leaves exactly five subgoals:

- output heap normalization for `replace_Znth k (Znth i_3 la 0) (lout_done_2 ++ sublist k (n_pre + m_pre) lo)`
- semantic prefix equality for `merge_sorted_arrays_spec (sublist 0 (i_3 + 1) la) (sublist 0 j_3 lb)`
- prefix length `Zlength (lout_done_2 ++ [Znth i_3 la 0]) = k + 1`
- preservation of consumed-`a`/future-`b` ordering
- preservation of consumed-`b`/future-`a` ordering

The correct helper-lemma decomposition is:

- `replace_Znth_app_suffix_head_Z`: if `Zlength prefix = k` and `0 <= k < n <= Zlength lo`, then writing at `k` in `prefix ++ sublist k n lo` rewrites to `(prefix ++ [x]) ++ sublist (k + 1) n lo`.
- `merge_one_last`: if every element of `b` is `< x`, then `merge_sorted_arrays_spec [x] b = b ++ [x]`.
- `merge_app_a_last`: if every element of `a` is `<= x` and every element of `b` is `< x`, then `merge_sorted_arrays_spec (a ++ [x]) b = merge_sorted_arrays_spec a b ++ [x]`.

These three lemmas were added to `coq/generated/merge_sorted_arrays_proof_manual.v` and compiled with `coqc`. `proof_of_merge_sorted_arrays_entail_wit_1` was also closed without `Admitted.` by choosing `nil` and rewriting `sublist 0 (n_pre + m_pre) lo` with `sublist_self`.

Important Coq detail: keep these helper lemmas before `Local Open Scope sac`; otherwise Coq rejects patterns like `induction b as [|...]` because `sac` changes parsing of intro-pattern notation. The stable form in this file avoids modern intro-pattern syntax and uses simple `induction b`/`rename` style.

## 2026-04-21 manual continuation: all generated proof obligations closed

The continuation focused only on `coq/generated/merge_sorted_arrays_proof_manual.v` in the existing workspace. The first issue was not a missing algorithmic invariant but a proof-layer tactic mismatch: for disjunctive entailments such as `entail_wit_3_1`, `entail_wit_3_2`, and `entail_wit_4`, using Coq's lowercase `left`/`right`/`exists` moved the proof into the model-level assertion and left the whole assertion as an open goal. The correct QCP proof style is uppercase `Left`/`Right` plus `Exists`, which keeps the proof at the entailment level so `entailer!` can solve the spatial frame.

After that, the remaining failures were hypothesis-indexing and explicit arithmetic/list-side-condition issues. The tail-copy `a` witness `entail_wit_4` needed the local hypothesis numbering after `pre_process` to be corrected: `H9` is `Zlength la = n_pre`, `H10` is `Zlength lb = m_pre`, `H11` is `Zlength lo = n_pre + m_pre`, `H12` is sortedness of `la`, `H14` is the consumed-`b`/future-`a` cross fact, `H16` is `Zlength lout_done_2 = k`, and `H17` is the semantic prefix equality. Once these were aligned, one manually written cross-boundary bullet was redundant because `j = m_pre` makes the side condition vacuous and `entailer!` already solved it.

The tail-copy `b` witness `entail_wit_6` had a different numbering because the invariant already contains `i = n_pre`: `H7` is `Zlength la = n_pre`, `H8` is `Zlength lb = m_pre`, `H9` is `Zlength lo = n_pre + m_pre`, `H11` is sortedness of `lb`, `H13` is the consumed-`a`/future-`b` cross fact, `H14` is `Zlength lout_done_2 = k`, and `H15` is the semantic prefix equality. This witness also required an explicit `Hn_nonneg : 0 <= n_pre` derived from `Zlength_nonneg`, because `lia` does not discover non-negativity of `Zlength la` through `H7` by itself. The post-write ordering side condition was proved by applying `H13`; the apparent consumed-`b`/future-`a` side condition was not a separate remaining goal after `entailer!`.

The final return witness was closed by deriving `j = m_pre`, substituting `i = n_pre`, deriving `k = n_pre + m_pre`, rewriting both consumed prefixes with `sublist_self`, rewriting the remaining suffix with `sublist_nil`, and then using the stored semantic equality for `lout_done`. No new axioms or `Admitted.` remain in `proof_manual.v`. Both `merge_sorted_arrays_proof_manual.v` and `merge_sorted_arrays_goal_check.v` compile.
