# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes
- Final result: `goal_check.v` compiles

## Issue 1: workspace fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` for `keywords`.
- Trigger: the workspace was initialized before task-specific semantic classification was filled in.
- Localization: `output/verify_20260419_230803_array_second_largest/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled `semantic_description` and controlled-vocabulary `keywords` for a read-only array selection scan with an empty-loop edge case.
- Result: fingerprint now uses only controlled keys and values, and `verification_status` is `goal_check_passed`.

## Issue 2: loop had no invariant for the second-largest accumulator semantics

- Phenomenon: the active annotated file initially had no invariant before `for (i = 2; i < n; ++i)`, so the verifier would not have a loop-head summary connecting `max1` / `max2` back to `second_largest_list(l)`.
- Trigger: the algorithm’s postcondition depends on the remaining suffix and the current two maxima, not just on scalar bounds.
- Localization: `annotated/verify_20260419_230803_array_second_largest.c`, loop before the scan body.
- Fix: added an `Extern Coq` declaration for `second_largest_acc` and an invariant preserving `2 <= i <= n`, `n == n@pre`, `a == a@pre`, `IntArray::full(a, n, l)`, and `second_largest_acc(max1, max2, sublist(i, n, l)) == second_largest_list(l)`.
- Result: rerunning `symexec` succeeded and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files for this workspace.

## Issue 3: initialization helper needed conservative destruct syntax

- Phenomenon: the first manual proof compile failed with `Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'`.
- Trigger: this Coq environment rejected compact destruct syntax such as `destruct l as [|x1 l']`.
- Localization: `coq/generated/array_second_largest_proof_manual.v`, initialization helper lemmas.
- Fix: rewrote list destructs using `destruct l`, explicit `rename`, and a `match goal` block for the second cons case.
- Result: compilation progressed into the semantic comparison proof.

## Issue 4: initialization contradiction branch needed explicit `Znth` normalization

- Phenomenon: `coqc` failed in `second_largest_list_init_le` with `Tactic failure: Cannot find witness`.
- Trigger: `simpl in Hle` did not reduce `Znth 1 (x1 :: x2 :: xs) 0` or `Znth 0 (x1 :: x2 :: xs) 0`, so `lia` could not see `x2 <= x1`.
- Localization: `coq/generated/array_second_largest_proof_manual.v`, `second_largest_list_init_gt` and `second_largest_list_init_le`.
- Fix: rewrote the hypotheses explicitly with `Znth_cons`, normalized `1 - 1`, then rewrote `Znth0_cons`.
- Result: both initialization helper lemmas compile.

## Issue 5: manual witnesses needed `pre_process` and delayed `entailer!`

- Phenomenon: after `left; entailer!`, the proof still had the whole antecedent as a model predicate, and later attempts to apply the helper lemma tried to solve the whole spatial goal.
- Trigger: the pure assumptions were not introduced before the proof tried to use them, and the accumulator equality was not asserted before solving the entailment frame.
- Localization: all ten manual witnesses in `coq/generated/array_second_largest_proof_manual.v`.
- Fix: started each witness with `pre_process`; asserted the needed pure fact (`Hspec`, `Hstep`, or `Hret`) before `entailer!`; used `entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto` to close residual shallow conjunctions.
- Result: initialization and loop entailment witnesses progressed past the spatial/pure framing failures.

## Issue 6: loop-step rewrite initially matched the wrong suffix occurrence

- Phenomenon: loop-step proofs failed when rewriting `second_largest_acc_sublist_step` because Coq tried to match the already-advanced suffix `sublist (i_2 + 1) n_pre l`.
- Trigger: rewriting the goal was ambiguous; the lemma should unfold the old invariant suffix `sublist i_2 n_pre l`, not the desired next-state suffix.
- Localization: `proof_of_array_second_largest_entail_wit_2_1` through `proof_of_array_second_largest_entail_wit_2_6`.
- Fix: rewrote the invariant hypothesis (`H3` or `H4`) with `second_largest_acc_sublist_step`, then destructed the generated `Z_gt_dec` branches and reused the rewritten hypothesis.
- Result: all six loop-preservation witnesses compile.

## Issue 7: return witness sublist lemma and equality direction

- Phenomenon: return witnesses first failed because `sublist_same` was unavailable, then because `replace ... in H2` generated the equality in the reverse direction.
- Trigger: this library exposes equal-bound sublists through `sublist_nil`, and the generated replace side goal was `nil = sublist n_pre n_pre l`.
- Localization: `proof_of_array_second_largest_return_wit_1` and `proof_of_array_second_largest_return_wit_2`.
- Fix: used `symmetry; apply sublist_nil; lia` to normalize the suffix to `nil`, then simplified `second_largest_acc max1 max2 nil`.
- Result: both return witnesses compile and prove `max2 = second_largest_list l`.

## Final outcome

- `symexec` succeeded on the latest annotated file.
- Full compile replay succeeded for `original/array_second_largest.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.
- `proof_manual.v` contains no `Admitted.` and no top-level `Axiom` declarations.
- Non-`.v` Coq intermediates under this workspace’s `coq/` directory were removed after the final compile.
