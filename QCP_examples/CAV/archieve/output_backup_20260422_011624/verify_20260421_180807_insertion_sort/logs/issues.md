
## 2026-04-21 verification issues

### Fingerprint initialization
- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: workspace bootstrap left the task-specific retrieval metadata blank.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md` and filled a non-empty semantic description plus controlled-vocabulary keywords for in-place insertion sort.
- Result: fingerprint metadata is non-empty and now records that manual witnesses are still needed.

### Invalid copied ordering invariant
- Phenomenon: the first generated `insertion_sort_entail_wit_1` required proving a prefix-to-suffix ordering property at `i == 1`, which is false for insertion sort on unsorted inputs.
- Trigger: the initial annotation reused a selection/bubble-sort partition invariant that does not hold for insertion sort.
- Localization: active annotated C outer-loop invariant before `for (i = 1; i < n; ++i)`.
- Fix: removed the prefix-to-suffix universal ordering from the outer and inherited inner invariants.
- Result: `symexec` regenerated obligations matching sorted-prefix insertion semantics.

### Skipped-loop boundary for `n == 0`
- Phenomenon: after removing the invalid ordering clause, `entail_wit_1` still required `1 <= n_pre`, contradicting the valid precondition case `n_pre == 0`.
- Trigger: the outer invariant used `i <= n@pre`, but the C `for` initializer sets `i = 1` before checking `i < n`.
- Localization: active annotated C outer-loop invariant bound.
- Fix: widened the invariant to `i <= n@pre + 1` and then strengthened it with `(n@pre > 0 => i <= n@pre)` so return can still recover `i == n` for nonempty arrays.
- Result: `symexec` succeeds with boundary-aware obligations; `entail_wit_1`, `entail_wit_2`, and `return_wit_1` are manually proved.

### Remaining insertion list witnesses
- Phenomenon: `coq/generated/insertion_sort_proof_manual.v` still contains `Admitted.` for `proof_of_insertion_sort_entail_wit_3`, `proof_of_insertion_sort_entail_wit_4_1`, and `proof_of_insertion_sort_entail_wit_4_2`.
- Trigger: these witnesses require list lemmas for the shifted-hole representation: one step of `replace_Znth (j+1) (Znth j l_cur) l_cur` must match the next hole state, and the final `replace_Znth (j+1) key l_cur` must be shown to be a permutation of the base list with a sorted prefix of length `i+1`.
- Localization: `coq/generated/insertion_sort_proof_manual.v`, remaining admitted theorem lines reported by `rg Admitted`.
- Fix attempted: completed the easier initialization and return witnesses and added reusable helper lemmas for one-element sorted prefixes and full-length sublists.
- Result: full Coq compilation can pass only because these three witnesses remain admitted; workflow success criteria are not met.

### Retry: base-list length missing from insertion invariant
- Phenomenon: after starting a direct proof of `proof_of_insertion_sort_entail_wit_3`, the one-step shift lemma needed `Zlength l_base = n_pre`, but the generated witness only exposed the heap length of the current `l_cur` state.
- Trigger: the inner invariant saved `l_base` as the outer-loop list but did not carry its length as a pure fact. This made sublist and `replace_Znth` normalization unnecessarily depend on reconstructing length from the shifted representation.
- Localization: active annotated C inner invariant for `while (j >= 0 && a[j] > key)`, and generated theorem `insertion_sort_entail_wit_3`.
- Fix: added `Zlength(l_outer) == n@pre` to the outer invariant and `Zlength(l_base) == n@pre` to the inner invariant, then reran `symexec` in the same workspace.
- Result: `symexec` succeeded and regenerated goals containing the needed length facts. `proof_of_insertion_sort_entail_wit_3` is now proved.

### Retry: final insertion witnesses still open
- Phenomenon: `proof_of_insertion_sort_entail_wit_4_1` and `proof_of_insertion_sort_entail_wit_4_2` remain admitted after the retry.
- Trigger: both witnesses require the full pure insertion lemma for the final `a[j + 1] = key` write: the resulting list must be a permutation of `l_base` and its prefix `sublist 0 (i + 1)` must be `sorted_z`. The `j >= 0` branch additionally needs to bridge `Znth j l_cur <= key` to the base-list boundary, while the `j < 0` branch needs the `j = -1` all-shifted case.
- Localization: `coq/generated/insertion_sort_proof_manual.v`, theorems `proof_of_insertion_sort_entail_wit_4_1` and `proof_of_insertion_sort_entail_wit_4_2`.
- Fix attempted: proved the regenerated initialization, inner-invariant initialization, inner shift preservation, and return witnesses; inspected the two remaining proof states after choosing `replace_Znth (j + 1) key l_cur` as the next outer list.
- Result: full Coq compilation including `goal_check.v` succeeds only because those two witnesses are still admitted. Workflow success criteria are not met.

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_180807_insertion_sort/logs/codex_stderr_20260421_183742.log`
- Detail: `external codex run exceeded remaining timeout budget of 1825 seconds`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_180807_insertion_sort/logs/codex_stderr_20260421_190807.log`
- Detail: `external codex run exceeded remaining timeout budget of 1 seconds`

### Retry: structural `sorted_z` invariant made final insertion proof too large
- Phenomenon: the final insertion witnesses were correct but hard to close because they required proving `sorted_z (sublist 0 (i + 1) (replace_Znth (j + 1) key l_cur))` directly from a shifted-hole list expression.
- Trigger: the loop invariants carried `sorted_z(sublist 0 i ...)`, which is semantically concise but proof-unfriendly for a local insertion step.
- Localization: active annotated C outer and inner invariants; generated witnesses `proof_of_insertion_sort_entail_wit_4_1` and `proof_of_insertion_sort_entail_wit_4_2`.
- Fix: replaced the invariant sorted-prefix fact with adjacent prefix order, reran `symexec`, and proved final insertion by local adjacent-pair case analysis. Added a return helper that derives `sorted_z` from adjacent order at loop exit.
- Result: all six manual witnesses are proved, `proof_manual.v` has no `Admitted.`, and `goal_check.v` compiles.

### Retry: final helper instantiation ambiguity
- Phenomenon: after the adjacent-order repair, `proof_of_insertion_sort_entail_wit_4_1` still failed at `Qed` with an incomplete proof.
- Trigger: broad `eapply` calls to final insertion helpers left Coq free to instantiate `l_base` with the stale outer-loop list `l_outer_2` instead of the inner invariant's base list `l_base`.
- Localization: `coq/generated/insertion_sort_proof_manual.v`, helper calls inside `proof_of_insertion_sort_entail_wit_4_1` and `_4_2`.
- Fix: explicitly passed `(l_base := l_base)`, `(l_cur := l_cur)`, `(key := key)`, and `(n := n_pre)` to the final insertion helper lemmas.
- Result: `proof_manual.v` compiled, and the full compile sequence through `goal_check.v` succeeded.

### Retry: helper lemma instantiated with stale outer list
- Phenomenon: after the adjacent-order invariant repair, `coqc` reported `Attempt to save an incomplete proof` at `coq/generated/insertion_sort_proof_manual.v:557` in `proof_of_insertion_sort_entail_wit_4_1`, even though the file no longer contained `Admitted.`.
- Trigger: the final insertion helper calls left list parameters partly implicit and then used broad `try eauto; try (symmetry; exact H6)` cleanup. In the length subgoal, Coq instantiated the helper lemma's `l_base` with the stale outer-loop list `l_outer_2` instead of the inner saved base list `l_base`.
- Localization: `proof_of_insertion_sort_entail_wit_4_1` and the analogous `_4_2` proof in `coq/generated/insertion_sort_proof_manual.v`.
- Fix: explicitly passed `(l_base := l_base)` and `(l_cur := l_cur)` to `insertion_sort_final_adj_ge`, `insertion_sort_final_adj_neg`, `insertion_sort_final_perm`, and `insertion_sort_final_Zlength`; solved the structural side condition with the inner invariant heap-shape hypothesis (`H10` in `_4_1`, `H9` in `_4_2`) rather than letting automation pick among similar lists.
- Result: `proof_manual.v` compiles, `goal_check.v` compiles, `proof_manual.v` has no `Admitted.` and no local `Axiom`, and non-`.v` Coq intermediate files were removed from the workspace.
