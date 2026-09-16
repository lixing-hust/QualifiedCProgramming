## Outcome

All nine target witnesses can enter proving in four independent groups. The three actual split goals are provable; the six targets without splits are provable as whole entailments. The likely longest groups are stopped-errors and success-result because they preserve spatial ownership while extracting an unsigned-byte range. Neither requires a new helper or a case library.

## Proof-Mode Decisions

The complete first pass considered only the three split goals: return_wit_1_split_goal_1, return_wit_2_split_goal_1, and return_wit_3_split_goal_1 are each provable. No top-level provability or strategy was considered during that pass.

In manual declaration order:

| Top-level suffix | Split result | Whole judgment | Mode and reason |
| --- | --- | --- | --- |
| return_wit_1 | One split, provable | Not analyzed | aggressive_pre_process: every split is provable |
| return_wit_2 | One split, provable | Not analyzed | aggressive_pre_process: every split is provable |
| return_wit_3 | One split, provable | Not analyzed | aggressive_pre_process: every split is provable |
| return_wit_4 | None | Provable | LLM_pre_process: zero grant mask selects the second disjunct |
| return_wit_5 | None | Provable | LLM_pre_process: same mask branch preserves the populated destination slot |
| return_wit_6 | None | Provable | LLM_pre_process: same mask branch preserves the null destination table entry |
| return_wit_7_callee_null | None | Provable | LLM_pre_process: the byte resource supplies the range needed for running = 0 |
| return_wit_8_callee_invalid | None | Provable | LLM_pre_process: stopped/invalid disjunct needs no fact about target |
| return_wit_11_callee_success | None | Provable | LLM_pre_process: stopped/success disjunct preserves the callee's updated fields |

All modes were fixed before developing the following strategies and groups. The final debug script covers exactly the three selected split goals and the six selected whole goals; the controller debug command terminated successfully with status passed. No previous sealed proving source is bound, so all strategies are from scratch and there are no reuse hints.

## Common Proof Patterns

**N — Nonzero truncation.** From unsigned_last_nbits running 32 <> 0 infer running <> 0 by assuming zero, substituting it, and computing the truncation. This is a pure implication with no range premise, heap resource, existential, or helper.

**D — Denial disjunction and unchanged frame.** Select the second postcondition disjunct, matching Z.land grant_right 64 = 0. Pattern N supplies running <> 0. The destination bound, nonnull current space, class branch and target branch are already pure premises. The seven common owned cells are OSTCBCur, its priority field, OSPrioCur, the current-space table entry, OSRunning, the grant-right slot field, and CapParent. Preserve and cancel these plus any destination resources; the RHS has no existential witnesses.

**Z — Stopped-state byte refinement.** The spatial OSRunning UChar cell semantically entails 0 <= running <= 255 while retaining the cell. Extract this range using the standard scalar points-to validity entailment. Since 255 < 2^32, unsigned_last_nbits running 32 equals running by modulo-small arithmetic; combine with the zero-truncation guard. Select the postcondition disjunct for running = 0, discharge existing pure premises, and reorder/cancel the same concrete resources. No new declaration is required: keep the small range/truncation argument inside each proof body. This step must precede any preprocessing that discards the scalar ownership fact.

## VC Deltas

- return_wit_1 split: N, using PreH3. The target = 0 branch does not affect the argument.
- return_wit_2 split: N, using PreH3. The target <> 0 branch is the only relevant context difference from the preceding split and is unused.
- return_wit_3 split: N, using PreH3. The class > 16 guard is unused.
- return_wit_4 whole: D, using PreH1 for the mask, PreH2 for N and PreH22 for class > 16; precisely seven unchanged cells.
- return_wit_5 whole: D; PreH22 gives class <= 16 and PreH23 target <> 0. Four extra cells are the destination table entry and the three fields holding old_type, old_content, and old_right. Preserve all eleven resources.
- return_wit_6 whole: D; PreH22 gives class <= 16 and PreH23 target = 0. Preserve the destination table cell in addition to the seven common cells.
- return_wit_7_callee_null whole: Z with guard PreH3. Choose RHS disjunct two; rewrite target using PreH24, so the callee's leading destination-table cell containing zero matches the trailing target-valued cell. Preserve all eight resources. The return value and class facts are already present.
- return_wit_8_callee_invalid whole: Z with guard PreH3. Choose RHS disjunct four; PreH23 gives class > 16. This branch deliberately avoids the unprovided target = 0 and permission/parent conditions of the other alternatives. All seven cells match.
- return_wit_11_callee_success whole: Z with guard PreH4. Choose RHS disjunct two; PreH24 and PreH25 give class <= 16 and target <> 0. The eleven resources are permuted between pre/post. The new slot values are already exactly 1, class, and Z.lor (Z.land old_right 4095) right in both heaps, so grant_cap_transition is not a missing premise or an obligation to re-prove mask algebra.

## Grouping Decisions

The initial grouping separated pure nonzero implications, permission-denied returns, and stopped callee returns by proof pattern and program branch. The second review separates the successful final-result entailment from the two stopped error returns because its destination update is independently provable and has no shared helper dependency.

| Group | Top-level VCs | Aggressive split goals | Difficulty | Load and coupling review |
| --- | --- | --- | --- | --- |
| running-nonzero | 3 | 3 | 1 | Pure truncation contradiction only; no spatial/context burden or helper |
| permission-denied | 3 | 0 | 1 | One uniform RHS choice, small pure facts, and unchanged scalar frames |
| stopped-errors | 2 | 0 | 2 | UChar range extraction and zero truncation; seven/eight-cell frames, no helper family |
| success-result | 1 | 0 | 2 | Independent final result; same small range argument plus an eleven-cell permutation and already-matching updated fields |

All groups have one proof mode. The singleton success-result group is justified by its independent final-result boundary. It shares only a small standard scalar-range argument with stopped-errors, not a new helper or persistent proof state; no group needs sibling output. Both potential tail groups use only the existing separation-logic and integer libraries. The success group has no independent safety or transition witness to split further, and no latent sum, length, permutation-of-lists, or mask helper workload. No helpers are planned because the fixed topology has no formal_case_lib.

## Risks or Blockers

No annotation, specification, resource, or dependency blocker was found. The material proof detail is the direction of truncation reasoning: zero truncation alone does not imply running = 0 over arbitrary integers. The three stopped whole VCs retain the necessary UChar ownership range, which must be used before simplifying their heaps. Formal files were read only; the debug artifact is the sole proof-state inspection source written in the bound build location.
