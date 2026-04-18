## Verification issues for `is_sorted_nondecreasing`

- Stage: `annotation`
  - Symptom: the first generated manual proof contained `proof_of_is_sorted_nondecreasing_safety_wit_2`, asking for `i + 1` to stay within signed-int range at loop head.
  - Trigger: the original loop invariant preserved `0 <= i <= n` and prefix sortedness, but did not preserve an explicit range fact for the expression `i + 1`.
  - Diagnosis: inspecting `is_sorted_nondecreasing_goal.v` showed `safety_wit_2` required `((i + 1) <= INT_MAX)`.
  - Fix: strengthened the invariant and loop-exit assertion with `i + 1 <= INT_MAX`, then cleared generated Coq files and reran `symexec`.
  - Result: `safety_wit_2` disappeared from `proof_manual.v`.

- Stage: `annotation`
  - Symptom: after the first annotation fix, the regenerated proof obligations still contained a nontrivial continue-branch entailment.
  - Trigger: `entail_wit_3` needed to prove the next-head bound `((i + 1) + 1) <= INT_MAX`.
  - Diagnosis: the branch assumptions exposed `i + 1 < n_pre`, but the invariant did not carry any explicit upper bound on `n_pre`, so the next-head range fact could not be recovered in pure Coq.
  - Fix attempt: strengthened the invariant and loop-exit assertion with `n <= INT_MAX` and reran `symexec`.
  - Result: `entail_wit_3` disappeared, but a new initialization obligation appeared in `entail_wit_1`.

- Stage: `proof / contract boundary`
  - Symptom: the current `proof_manual.v` still cannot be completed.
  - Trigger: the regenerated `entail_wit_1` now requires proving `n_pre <= INT_MAX` from the function precondition alone.
  - Diagnosis: the current input contract does not state any upper bound on `n`, and the generated initialization witness does not retain the local `n` store, so Verify has no authorized way to derive that bound. This makes the strengthened invariant unprovable from the formal input.
  - Fix action considered: changing `input/is_sorted_nondecreasing.c` to add `n <= INT_MAX` (or a tighter bound) would likely unblock the proof, but that is a Contract-stage modification and is outside Verify permissions.
  - Result: verification remains blocked at the formal-input boundary. `goal_check.v` has not been compiled successfully end to end.

- Files produced successfully before the blocker:
  - `logs/qcp_run.log`
  - `coq/generated/is_sorted_nondecreasing_goal.v`
  - `coq/generated/is_sorted_nondecreasing_proof_auto.v`
  - `coq/generated/is_sorted_nondecreasing_proof_manual.v`
  - `coq/generated/is_sorted_nondecreasing_goal_check.v`

- Compile status:
  - `goal.v` compiled
  - `proof_auto.v` compiled
  - `proof_manual.v` failed with an incomplete proof at `proof_of_is_sorted_nondecreasing_entail_wit_1`
  - `goal_check.v` was not compiled successfully after the manual-proof failure

- Relevant logs:
  - `logs/qcp_run.log`
  - `logs/compile_goal.log`
  - `logs/compile_proof_auto.log`
  - `logs/compile_proof_manual.log`
