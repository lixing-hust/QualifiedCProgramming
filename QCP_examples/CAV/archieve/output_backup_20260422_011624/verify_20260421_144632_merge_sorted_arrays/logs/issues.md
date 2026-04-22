## 2026-04-21 symexec: missing initial loop assertions

- Phenomenon: the first clean `symexec` run on the unmodified annotated file failed at `annotated/verify_20260421_144632_merge_sorted_arrays.c:35:4` with `Error: Lack of assertions in some paths for the loop!`.
- Trigger: `merge_sorted_arrays` has three `while` loops and the annotated copy initially had no loop invariants.
- Localization: first `while (i < n && j < m)` at the merge loop, with two later tail-copy loops also requiring loop-head invariants.
- Fix action: added loop invariants to the annotated working copy and reran `symexec` after each annotation change as required.
- Result: the initial missing-assertion error was replaced by later invariant-shape and entailment failures.

## 2026-04-21 symexec: recursive semantic invariant caused frontend blow-up

- Phenomenon: after adding semantic prefix/suffix invariants containing `merge_sorted_arrays_spec(sublist(...), sublist(...))`, `symexec` ran for roughly 50 seconds with an empty `logs/qcp_run.log` and zero-byte generated files.
- Trigger: the recursive Coq merge spec was placed directly in all three loop invariants together with output prefix/suffix facts.
- Localization: the three `Inv` blocks in `annotated/verify_20260421_144632_merge_sorted_arrays.c` before each `while` loop.
- Fix action: stopped the CPU-bound `symexec` process, removed the recursive spec equality and suffix-value facts, and reran from a clean generated directory.
- Result: the frontend still ran too long, so the invariant was reduced further.

## 2026-04-21 symexec: pre-state arithmetic in ownership was too expensive

- Phenomenon: reduced invariants using `exists lout` but lengths such as `n@pre + m@pre` still caused `symexec` to run more than 30 seconds without writing normal startup output.
- Trigger: invariant ownership used pre-state arithmetic expressions in `IntArray::full(out, n@pre + m@pre, lout)` and related bounds.
- Localization: all three loop invariants in the annotated file.
- Fix action: rewrote the weak ownership invariants to use current `n`, `m`, and `n + m` in bounds and array lengths.
- Result: `symexec` produced a normal entailment diagnostic after about 33 seconds, confirming that current-state arithmetic is a more tractable annotation shape for this task.

## 2026-04-21 symexec: second loop invariant was too strong at loop entry

- Phenomenon: with current-state arithmetic, `symexec` failed when initializing the second loop invariant. The diagnostic showed the verifier trying to establish `j == m` and output/input ownership at the head of `while (i < n)`.
- Trigger: the second loop invariant assumed `j == m` and `k == i + m`, but the program reaches that loop head even on paths where the first loop exited because `i == n` while `j < m`; the loop guard has not yet been consumed at invariant initialization.
- Localization: the invariant immediately before `while (i < n)` in `annotated/verify_20260421_144632_merge_sorted_arrays.c`.
- Fix action: weakened the second loop invariant to the general relation `0 <= i <= n`, `0 <= j <= m`, and `k == i + j`.
- Result: the next `symexec` attempt became CPU-bound again for over 80 seconds with an empty log and zero-byte generated files. The run was stopped due to the external time budget, so verification did not reach the proof stage.

## 2026-04-21 final status

- `symexec` did not succeed on the latest annotated file.
- No usable fresh `goal`, `proof_auto`, `proof_manual`, or `goal_check` files were produced by the latest run.
- Manual proof was not attempted because the workflow never reached a successful symbolic execution result.

## 2026-04-21 retry: symexec repaired, proof remains open

- Phenomenon: replacing the weak whole-array existential invariant with `IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))` and adding the semantic prefix equality allowed `symexec` to complete successfully in the same workspace. Fresh generated files were produced under `coq/generated/`.
- Trigger repaired: the previous `exists lout` full-array invariant caused `symexec` to stay CPU-bound with an empty log and zero-byte generated files. Segment-only invariants also failed because the strategy did not split `IntArray::full` into full-length `IntArray::seg` goals at loop initialization.
- Current blocker: manual proof is not complete. The first compile attempt with standard witnesses failed in `coq/generated/merge_sorted_arrays_proof_manual.v` at `proof_of_merge_sorted_arrays_entail_wit_1` with `Attempt to save an incomplete proof`. A `coqtop` probe showed the remaining first subgoal is the heap equality `IntArray.full out_pre (n_pre + m_pre) lo |-- IntArray.full out_pre (n_pre + m_pre) (nil ++ sublist 0 (n_pre + m_pre) lo)`, which needs explicit `sublist_self`/length normalization. Later witnesses will also need helper lemmas for `replace_Znth` at the end of the written prefix and for the recurrence of `merge_sorted_arrays_spec` over sorted prefixes.
- Localization: `merge_sorted_arrays_proof_manual.v` currently contains attempted skeleton proofs for `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_4`, `entail_wit_6`, and `return_wit_1`; `coqc` stops at the first one.
- Fix action completed this round: repaired annotation enough for VC generation, generated fresh Coq files, inspected the first proof state, and removed non-`.v` Coq compilation artifacts after the failed compile.
- Result: verification is still `Fail` because `proof_manual.v` and `goal_check.v` do not compile yet. No `Admitted.` or new `Axiom` lines remain in `proof_manual.v`, but the attempted proofs are incomplete.

## 2026-04-21 retry: proof exposed missing two-pointer history invariant

- Phenomenon: after the previous successful `symexec`, `coqc` stopped at `coq/generated/merge_sorted_arrays_proof_manual.v:36:0-4` in `proof_of_merge_sorted_arrays_entail_wit_2_1` with `Attempt to save an incomplete proof`.
- Trigger: the generated VC for the branch that writes `a[i]` required proving `lout_done_2 ++ [Znth i_3 la 0] = merge_sorted_arrays_spec (sublist 0 (i_3 + 1) la) (sublist 0 j_3 lb)`. The old invariant recorded only the merge of consumed prefixes, not the two-pointer ordering history needed to justify appending the current element at the end of the merged prefix.
- Localization: first-loop preservation witnesses `entail_wit_2_1` and `entail_wit_2_2`, with the same semantic issue later in the two tail-copy loops.
- Fix action: added cross-boundary ordering facts to all loop invariants: consumed `b` elements are strictly less than future `a` elements, and consumed `a` elements are less-or-equal to future `b` elements. Also added `n == n@pre` and `m == m@pre` so return witnesses connect current loop-state lengths to contract lengths.
- Result: the invariant repair changed the proof obligations to the right semantic shape, but manual Coq helper lemmas for the recursive merge spec are still needed.

## 2026-04-21 retry: frontend rejected free guarded list indexing in invariant

- Phenomenon: the first cross-boundary annotation repair made `symexec` fail at `annotated/verify_20260421_144632_merge_sorted_arrays.c:89:4` with `Cannot infer size of array`.
- Trigger: the invariant used bracket notation with a free loop index, e.g. `lb[p] <= la[i]`, guarded by `(i < n) => ...`. At a loop head `i` may equal `n`, and the frontend did not use the implication guard to infer the ghost-list access size.
- Localization: second loop invariant immediately before `while (i < n)`.
- Fix action: rewrote the facts as quantified range facts over future indices so each access has a bound in the quantified antecedent.
- Result: this removed the size-inference failure but exposed a second frontend issue with bracket notation on ghost lists.

## 2026-04-21 retry: frontend mis-typed quantified bracket notation on ghost lists

- Phenomenon: after the quantified range rewrite, `symexec` failed after partial VC generation with `The array q_167 of Znth is not a list type. The type is Z`, and then again with the renamed variable as `ai_167`.
- Trigger: bracket notation such as `la[ai]` inside the quantified invariant facts was mis-typed by the frontend in this context.
- Localization: the two cross-boundary quantified facts in all three loop invariants/loop-exit assertions.
- Fix action: replaced bracket notation with explicit Coq-style calls `Znth(index, list, 0)` in these pure facts.
- Result: `symexec` succeeded again and produced fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## 2026-04-21 retry current blocker: merge-spec helper lemmas missing

- Phenomenon: after replacing generated `Admitted.` placeholders with honest proof skeletons, full compile replay still stops at `merge_sorted_arrays_proof_manual.v:36:0-4` in `proof_of_merge_sorted_arrays_entail_wit_2_1` with `Attempt to save an incomplete proof`.
- Trigger: `entailer!` leaves five subgoals for `entail_wit_2_1`: output `replace_Znth` normalization, merge-prefix semantic equality, prefix length, and preservation of the two cross-boundary ordering facts.
- Localization: `coq/generated/merge_sorted_arrays_proof_manual.v`, theorem `proof_of_merge_sorted_arrays_entail_wit_2_1`; the same helper pattern will be needed for `entail_wit_2_2`, `entail_wit_4`, `entail_wit_6`, and `return_wit_1`.
- Fix action completed: proved `entail_wit_1`, removed all manual `Admitted.` placeholders, cleaned Coq non-`.v` artifacts after the failed compile, and recorded the missing helper-lemma blocker.
- Result: verification remains `Fail`: `symexec` succeeds, `goal.v` and `proof_auto.v` compile, but `proof_manual.v` and `goal_check.v` do not compile yet.

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_144632_merge_sorted_arrays/logs/codex_stderr_20260421_152328.log`
- Detail: `external codex run exceeded remaining timeout budget of 1384 seconds`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_144632_merge_sorted_arrays/logs/codex_stderr_20260421_154632.log`
- Detail: `external codex run exceeded remaining timeout budget of 1 seconds`

## 2026-04-21 manual continuation: lowercase disjunction tactics left open goals

- Phenomenon: `coqc` failed in `proof_of_merge_sorted_arrays_entail_wit_3_1` with `Attempt to save an incomplete proof`, even though the branch choice and existential witness looked syntactically correct.
- Trigger: the proof used lowercase `right` and lowercase `exists` after `pre_process`. In QCP entailment proofs this enters the model-level disjunction/existential and leaves the entire target assertion applied to a model as an open goal.
- Localization: `coq/generated/merge_sorted_arrays_proof_manual.v`, witnesses `entail_wit_3_1`, `entail_wit_3_2`, and `entail_wit_4`.
- Fix action: replaced lowercase branch tactics with QCP tactics `Right`/`Left` and `Exists`; also substituted the exit equality (`j = m_pre` or `i = n_pre`) before choosing the branch.
- Result: the disjunctive transition witnesses progressed to the actual list/arithmetic side conditions.

## 2026-04-21 manual continuation: generated hypothesis numbers differed by witness

- Phenomenon: several compile errors reported missing rewrite subterms, for example `Found no subterm matching "Zlength lb"` or `Found no subterm matching "Znth ?z la 0"`.
- Trigger: proof fragments copied from the main merge loop used hypothesis numbers from `entail_wit_2_1`/`2_2`, but `pre_process` creates different numbering in tail-copy witnesses where some loop facts are absent or already specialized.
- Localization: `entail_wit_4` and `entail_wit_6`.
- Fix action: inspected each witness with `coqtop Show` and rewired the proof to the actual local hypotheses. In `entail_wit_4`, length/sortedness/cross facts came from `H9`, `H10`, `H11`, `H12`, `H14`, `H16`, `H17`. In `entail_wit_6`, they came from `H7`, `H8`, `H9`, `H11`, `H13`, `H14`, `H15`.
- Result: both tail-copy witnesses compile without relying on guessed hypothesis names.

## 2026-04-21 manual continuation: non-negativity of length was implicit

- Phenomenon: `entail_wit_6` failed with `Cannot find witness` while proving a `Forall_sublist0_Znth_le_value` side condition.
- Trigger: the proof needed `0 <= n_pre`, but this witness only provided `Zlength la = n_pre`; `lia` does not automatically derive non-negativity from `Zlength`.
- Localization: `entail_wit_6`, proof of `Forall (fun z => z <= Znth j lb 0) (sublist 0 i la)`.
- Fix action: added `Hn_nonneg : 0 <= n_pre` by rewriting from `H7 : Zlength la = n_pre` and applying `Zlength_nonneg`.
- Result: the sublist side condition became solvable by `lia`.

## 2026-04-21 manual continuation: final return needed explicit full-prefix rewrites

- Phenomenon: `return_wit_1` was still admitted after the other witnesses compiled.
- Trigger: the final state stores `lout_done = merge_sorted_arrays_spec (sublist 0 i la) (sublist 0 j lb)` and the heap stores `lout_done ++ sublist k (n_pre + m_pre) lo`; the postcondition needs full `la`, full `lb`, and no suffix.
- Localization: `proof_of_merge_sorted_arrays_return_wit_1`.
- Fix action: derived `j = m_pre`, substituted `i = n_pre`, derived `k = n_pre + m_pre`, rewrote `sublist 0 n_pre la` and `sublist 0 m_pre lb` with `sublist_self`, rewrote the output suffix with `sublist_nil`, then used the semantic equality for `lout_done`.
- Result: `return_wit_1` is now a real proof; `proof_manual.v` and `goal_check.v` compile.
