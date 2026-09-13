# Outcome

All 10 top-level witnesses are provable and can enter proving in four independent groups. Four witnesses use `aggressive_pre_process` (four selected split goals total); six use `LLM_pre_process`. The expected critical path is `cap-update-success` because it combines the inner successful capability update with the outer successful-call frame, although both selected goals were independently tactic-checked. No helper or reuse work is available in this topology.

# Proof-Mode Decisions

1. `proof_of_ucos_Grant_Cap_return_wit_1_valid_target`: split `..._split_goal_spatial` is **provable**; select `aggressive_pre_process` and do not analyze the whole top-level VC.
2. `proof_of_grant_cspace_cap_return_wit_1`: split `..._split_goal_1` is **provable**; select `aggressive_pre_process` and do not analyze the whole top-level VC.
3. `proof_of_grant_cspace_cap_return_wit_2`: split `..._split_goal_1` is **provable**; select `aggressive_pre_process` and do not analyze the whole top-level VC.
4. `proof_of_grant_cspace_cap_return_wit_3`: split `..._split_goal_1` is **provable**; select `aggressive_pre_process` and do not analyze the whole top-level VC.
5. `proof_of_grant_cspace_cap_return_wit_4`: no split; the whole goal is **provable**, so select `LLM_pre_process`.
6. `proof_of_grant_cspace_cap_return_wit_5`: no split; the whole goal is **provable**, so select `LLM_pre_process`.
7. `proof_of_grant_cspace_cap_return_wit_6`: no split; the whole goal is **provable**, so select `LLM_pre_process`.
8. `proof_of_grant_cspace_cap_return_wit_7_callee_null`: no split; the whole goal is **provable**, so select `LLM_pre_process`.
9. `proof_of_grant_cspace_cap_return_wit_8_callee_invalid`: no split; the whole goal is **provable**, so select `LLM_pre_process`.
10. `proof_of_grant_cspace_cap_return_wit_11_callee_success`: no split; the whole goal is **provable**, so select `LLM_pre_process`.

The final controller debug script covered exactly these four split targets and six whole-goal targets. Each was checked non-destructively with `intros; pre_process; entailer!` and the controller returned `status: passed`.

# Common Proof Patterns

- **P1 — Bit observation:** `unsigned_last_nbits running 32 <> 0` refutes `running = 0`. Conversely, where the observation is zero, preprocessing uses the byte-valued `OSRunning` points-to resource to recover the bounded representation and establish `running = 0`.
- **P2 — Indexed-address normalization:** rewrite `destTask_Prio_pre = dest` (and, for the inner call, `cap_Class_pre = class` and `cap_Right_pre = right`) before spatial cancellation so the indexed `CapParent`, destination-table, and capability-field addresses match syntactically.
- **P3 — Branch-and-frame entailment:** choose the postcondition disjunct whose pure guard is already present, discharge constant/pure projections, and cancel the unchanged points-to frame modulo associativity/commutativity of separating conjunction.

# VC Deltas

- `proof_of_ucos_Grant_Cap_return_wit_1_valid_target` / selected spatial split: P2+P3. `P` owns the destination table cell plus updated `cap_type`, category content, and category right cells; `Q` owns exactly those four cells after parameter equalities normalize their addresses and values. There are no existentials or refinement states.
- `proof_of_grant_cspace_cap_return_wit_1`, `_2`, `_3` / selected pure splits: P1 only. Each goal has no spatial postcondition or existential; the sole delta is the surrounding branch data (`target = 0`, nonnull target with its old capability cells, or invalid class), which does not enter the selected split proof.
- `proof_of_grant_cspace_cap_return_wit_4`: P1+P2+P3. Choose the `Z.land grant_right 64 = 0` branch. `P` and `Q` share the scheduler/current-space/right-cell/CapParent resources, and all post pure facts come from premises or P1.
- `proof_of_grant_cspace_cap_return_wit_5`: P1+P2+P3 with the nonnull destination table cell and three unchanged target capability fields added to the common spatial frame.
- `proof_of_grant_cspace_cap_return_wit_6`: P1+P2+P3 with the null destination table cell added to the common frame; choose the bit-clear/null-target branch.
- `proof_of_grant_cspace_cap_return_wit_7_callee_null`: P1+P2+P3, choosing the running-zero/null-target/class-valid branch. The post reuses the destination table, scheduler, right-cell, and CapParent ownership; no ownership is synthesized.
- `proof_of_grant_cspace_cap_return_wit_8_callee_invalid`: P1+P2+P3, choosing the running-zero/class-invalid branch. Its spatial frame omits the destination table cell, matching `P` exactly.
- `proof_of_grant_cspace_cap_return_wit_11_callee_success`: P1+P2+P3, choosing the running-zero successful-call branch. `P` already owns the modified target capability fields and all scheduler/table/CapParent resources required by `Q`; the result has no existential or abstract refinement transition.

No VC needs a mathematical helper: all pure obligations and spatial transformations are discharged from current premises/resources, and the fixed topology has no editable case library.

# Grouping Decisions

The initial groups follow program phase and persistent spatial context: inner/outer capability-update success, three active-running return projections, three grant-bit-clear direct returns, and two callee error returns.

The second review keeps group sizes at 2/3/3/2, below the hard limit and within the preferred range. `active-return-projections` has three lightweight aggressive pure splits, no spatial load, no helper family, and difficulty 1. `grant-bit-clear-returns` has three LLM whole goals sharing the same disjunction choice, bit observation, scheduler frame, and index normalization; the target-specific resources vary but do not justify separate contexts, so difficulty 2. `callee-error-returns` has two LLM whole goals sharing the zero-running derivation and callee-return frame; difficulty 2.

`cap-update-success` is the likely tail: two top-level witnesses, one aggressive spatial split, one LLM whole goal, no helper/library load, but the largest sustained spatial context (destination table plus updated capability fields and scheduler frame) and mixed proof modes. The inner update and outer successful-call result are kept together because both center on the same modified capability resources; splitting would create two small groups without reducing any helper or library bottleneck. Difficulty is 3. Final-result work is otherwise separated from independent grant-bit-clear and callee-error transitions.

# Risks or Blockers

No blocker was found. The main execution risk is syntactic normalization of indexed addresses and nested separating conjunctions, but the controller-backed tactic checks closed every selected target. Reuse is intentionally absent because no eligible immediately preceding sealed proving source was bound.
