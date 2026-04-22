# Proof Reasoning

## 2026-04-19T23:10:00+0800: classify generated manual obligations

Fresh `symexec` generated ten manual obligations in `array_second_largest_proof_manual.v`:

- Initialization witnesses `entail_wit_1_1` and `entail_wit_1_2`, which must connect the first two initialized maxima to `second_largest_list l`.
- Loop-preservation witnesses `entail_wit_2_1` through `entail_wit_2_6`, which must show that one scan step preserves the accumulator invariant after a branch update.
- Return witnesses `return_wit_1` and `return_wit_2`, which must use `i_2 >= n_pre`, `i_2 <= n_pre`, and the invariant to prove `max2 = second_largest_list l`.

These are pure list/specification obligations plus separation-logic frame preservation. The useful helper fact is that, when `i < n` and `Zlength l = n`, the suffix `sublist i n l` can be unfolded into `Znth i l 0 :: sublist (i + 1) n l`; after that, each loop witness follows by simplifying `second_largest_acc` and choosing the side of the generated disjunction matching the preserved initial comparison branch. Return witnesses need `i_2 = n_pre`, then `sublist n_pre n_pre l = nil`, so the invariant simplifies to exactly `max2 = second_largest_list l`.

The first proof edit will add conservative helper lemmas for the suffix unfold, initialization of `second_largest_list`, one-step accumulator preservation, and return simplification, then use short witness scripts around `entailer!`.

## 2026-04-19T23:11:00+0800: first compile failure in helper destruct syntax

The first compile attempt stopped in `array_second_largest_proof_manual.v` before reaching any semantic witness:

- File: `coq/generated/array_second_largest_proof_manual.v`
- Line: 99
- Error: `Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'`

The environment rejects the compact `destruct l as [|x1 l']` syntax in this context. This is a Coq-script compatibility issue, not a proof-state issue. I rewrote both initialization helper lemmas to use the repository's conservative pattern: `destruct l`, then `rename z into ...`, then `destruct l'`, then rename the generated head and tail through a `match goal` block.

## 2026-04-19T23:12:00+0800: second compile failure in initialization contradiction

After the syntax rewrite, `coqc` reached the `second_largest_list_init_le` helper and failed at the contradiction branch with:

- File: `coq/generated/array_second_largest_proof_manual.v`
- Line: 143
- Error: `Tactic failure: Cannot find witness`

I probed the local proof state with `coqtop`. The key finding is that `simpl in Hle` does not unfold `Znth 1 (x1 :: x2 :: xs) 0` or `Znth 0 (x1 :: x2 :: xs) 0` in this environment, so `lia` sees an opaque comparison rather than `x2 <= x1`. I replaced the ineffective `simpl` step with explicit `Znth_cons` and `Znth0_cons` rewrites in both initialization helper lemmas before the comparison case split.

## 2026-04-19T23:13:00+0800: third compile failure because pure facts were not introduced

After fixing `Znth` normalization, the next failure moved to `proof_of_array_second_largest_entail_wit_1_1`:

- File: `coq/generated/array_second_largest_proof_manual.v`
- Line: 157
- Error: `Tactic failure: Cannot find witness`

The `coqtop` proof state after `left; entailer!` still had the entire antecedent as a model predicate `H : (...) m`; the pure facts such as `Zlength l = n_pre` had not been introduced as Coq hypotheses, so `replace n_pre with (Zlength l) by lia` had no length equality available. I changed the generated witness proofs to start with `pre_process`, following the repository examples, so pure facts are extracted before `entailer!`.

## 2026-04-19T23:14:00+0800: fourth compile failure because `entailer!` was called too early

With `pre_process` in place, the failure moved but still occurred inside `proof_of_array_second_largest_entail_wit_1_1`. The proof state showed normal hypotheses:

- `H : Znth 1 l 0 > Znth 0 l 0`
- `H0 : 2 <= n_pre`
- `H1 : Zlength l = n_pre`
- `H3 : IntArray.full a_pre n_pre l m`

However, after `left; entailer!`, the remaining goal was still a large model predicate containing all pure conjuncts and the spatial array fact. Applying `second_largest_list_init_gt` at that point tried to solve the whole predicate, not only the accumulator equality. I restructured each witness to first assert the needed pure accumulator equality (`Hspec`, `Hstep`, or `Hret`), and only then call `entailer!` to finish the conjuncts and frame.

## 2026-04-19T23:15:00+0800: fifth compile failure because residual shallow conjunctions remained

After asserting the pure facts first, `coqc` reported an incomplete proof at the end of `proof_of_array_second_largest_entail_wit_1_1`. A `coqtop` `Show` after `entailer!` showed that the remaining goal was a shallow model-level conjunction of pure facts plus `IntArray.full`; all needed facts were already present (`H`, `H0`, `H2`, `Hspec`, and the spatial hypothesis). I extended the witness endings to run `simpl; repeat split; try lia; auto` after `entailer!` so these residual shallow conjunctions are discharged explicitly.

## 2026-04-19T23:16:00+0800: sixth compile failure from rewriting the wrong suffix occurrence

After the shallow-conjunction cleanup was fixed to unfold the imported `coq_prop` / `andp`, the compile reached `proof_of_array_second_largest_entail_wit_2_1` and failed at the loop-step rewrite. A `coqtop` probe showed that `rewrite second_largest_acc_sublist_step by lia` tried to match the already-advanced left-hand side `sublist (i_2 + 1) n_pre l`, creating an unprovable side condition `i_2 + 1 < n_pre`. The intended rewrite is on the invariant hypothesis `H3` / `H4`, whose suffix is still `sublist i_2 n_pre l`. I changed all six loop-step witnesses to rewrite the invariant hypothesis first, then destruct the generated `Z_gt_dec` branches and reuse the rewritten hypothesis directly.

## 2026-04-19T23:25:54+0800: final proof and compile result

The next proof failures were local Coq-library and syntax issues:

- Empty branch syntax `[lia |]` was rejected, so the affected `Z_gt_dec` splits were rewritten with bullets.
- The return witnesses initially tried `sublist_same`, which is not available in this environment. The correct equal-bound lemma here is `sublist_nil`.
- `replace ... with ... in H2` produced the side equality in reverse direction, so the proof uses `symmetry; apply sublist_nil; lia`.

After these changes, `array_second_largest_proof_manual.v` compiled successfully. The full documented replay also compiled `original/array_second_largest.v`, `array_second_largest_goal.v`, `array_second_largest_proof_auto.v`, `array_second_largest_proof_manual.v`, and `array_second_largest_goal_check.v`. A final grep found no `Admitted.` and no top-level `Axiom` declarations in `proof_manual.v`.
