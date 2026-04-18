# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: active annotated copy used unsupported `With` binder syntax

- Phenomenon:
  - the first `symexec` run failed at the contract header with:
    - `unexpected PT_COMMA, expecting PT_REQUIRE`
- Trigger:
  - this front end rejects comma-separated binders in `With`
- Localization:
  - `annotated/verify_20260418_211226_array_adjacent_diff.c`
- Fix:
  - normalized only the active annotated copy from `With la, lo` to `With la lo`
- Result:
  - `symexec` advanced past parsing and reached loop analysis

## Issue 2: the loop initially had no loop-head summary

- Phenomenon:
  - the next `symexec` run failed with:
    - `Error: Lack of assertions in some paths for the loop!`
- Trigger:
  - the output-writing loop needed an invariant describing the processed prefix of adjacent differences and the untouched suffix of `out`
- Localization:
  - `annotated/verify_20260418_211226_array_adjacent_diff.c`
- Fix:
  - added an invariant with:
    - `0 <= i <= n@pre - 1`
    - unchanged `a`, `out`, and `n`
    - a processed prefix list `l1`
    - `IntArray::full(out, n@pre - 1, app(l1, sublist(i, n@pre - 1, lo)))`
- Result:
  - `symexec` progressed into real VC generation

## Issue 3: loop-body bridges were overconstraining the store step

- Phenomenon:
  - two successive annotation attempts failed inside loop-body `which implies` blocks during partial solve
- Trigger:
  - the front end already had the correct `replace_Znth` heap update after `out[i] = a[i + 1] - a[i]`, but the explicit bridges forced premature list normalization
- Localization:
  - loop-body annotations in `annotated/verify_20260418_211226_array_adjacent_diff.c`
- Fix chain:
  - first simplified the untouched suffix from an existential `l2` to the canonical `sublist(i, n@pre - 1, lo)`
  - then removed both loop-body `which implies` blocks entirely
- Result:
  - `symexec` succeeded on the annotated file

## Issue 4: loop-exit assertion generated an unnecessary local-store proof obligation

- Phenomenon:
  - the first proof iteration reached a witness whose left-hand heap still contained the live local `n` store
- Trigger:
  - the loop-exit assertion was repackaging state at a control point where local-variable cleanup had not happened yet
- Diagnosis:
  - `coqtop` showed the resulting entailment had to prove away the extra `&( "n" ) # Int |-> n_pre` resource
- Fix:
  - removed the loop-exit assertion from the annotated file
  - cleared generated Coq files
  - reran `symexec`
- Result:
  - the regenerated VC dropped that problematic entailment and left only four standard manual obligations

## Issue 5: helper proof for the loop-step witness needed stable list-normalization tactics

- Phenomenon:
  - early compile attempts on `array_adjacent_diff_proof_manual.v` failed in the local helper lemma for the step witness
- Trigger chain:
  - `sublist` side conditions needed `Zlength_correct`
  - this Coq version rejected the newer induction syntax
  - direct `reflexivity` did not finish the final appended-list normalization
- Fix chain:
  - used `rewrite Zlength_correct in Hlo` in the `sublist_split` / `sublist_single` side conditions
  - replaced the local induction with `replace_Znth_nothing`
  - finished the last equality with explicit `simpl` and `app_assoc`
- Result:
  - the helper lemma `adjacent_diff_step_list` compiled and the step witness proof stabilized

## Issue 6: proof scripts needed proof-state inspection after `entailer!`

- Phenomenon:
  - compile-driven edits on the manual witnesses initially used the wrong subgoal order and stale hypothesis names
- Trigger:
  - after `entailer!`, the remaining goals were not in the order suggested by the first draft proof
- Diagnosis:
  - `coqtop` inspection showed:
    - `entail_wit_2` leaves the prefix property first and the length goal second
    - the regenerated `return_wit_1` only needed `i_3 = n_pre - 1`, `sublist_nil`, and the existing prefix property hypothesis
- Fix:
  - reordered the witness bullets
  - stopped relying on unstable numbered hypotheses where possible
  - rewrote the final return witness to use the regenerated proof-state shape
- Result:
  - `array_adjacent_diff_proof_manual.v` compiled
  - `array_adjacent_diff_goal_check.v` compiled

## Final outcome

- `symexec` succeeded on the latest annotated file.
- `array_adjacent_diff_goal.v`, `array_adjacent_diff_proof_auto.v`, `array_adjacent_diff_proof_manual.v`, and `array_adjacent_diff_goal_check.v` all compiled successfully.
- `array_adjacent_diff_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the final compile replay.
