# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Symexec invocation recovery

- Phenomenon: the first manual `symexec` retry only wrote `goal file not specified` and did not generate usable Coq artifacts.
- Trigger: I initially invoked `symexec` without the repository’s required explicit output-file flags.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_170027_array_contains/logs/qcp_run.log`
- Fix:
  - switched to the canonical invocation shape used elsewhere in this repo
  - passed:
    - `--goal-file`
    - `--proof-auto-file`
    - `--proof-manual-file`
    - `--input-file`
    - `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`
    - `--coq-logic-path=SimpleC.EE.CAV.verify_20260418_170027_array_contains`
    - `--no-exec-info`
- Result: later runs produced fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Annotation layer

- Phenomenon: the first real `symexec` pass failed with `Error: Lack of assertions in some paths for the loop!`.
- Trigger: the scan loop had no invariant describing the processed prefix, so the verifier had no loop-head summary for the no-hit path.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_170027_array_contains.c`
- Fix:
  - added a loop invariant with:
    - `0 <= i && i <= n`
    - `a == a@pre`
    - `n == n@pre`
    - `k == k@pre`
    - `(forall (j: Z), (0 <= j && j < i) => l[j] != k)`
    - `IntArray::full(a, n, l)`
  - added a loop-exit assertion fixing:
    - `i == n`
    - the same unchanged-parameter facts
    - full-prefix non-membership `(forall (j: Z), (0 <= j && j < n) => l[j] != k)`
- Result: rerunning `symexec` succeeded and `qcp_run.log` ended with `Successfully finished symbolic execution`.

## Manual proof iteration

- Phenomenon: the generated `array_contains_proof_manual.v` contained two `Admitted.` placeholders:
  - `proof_of_array_contains_return_wit_1`
  - `proof_of_array_contains_return_wit_2`
- Trigger: the early-return and loop-exit semantics both require pure list reasoning about `array_contains_spec`, which the auto proof did not discharge.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_170027_array_contains/coq/generated/array_contains_proof_manual.v`
- Fix chain:
  - added two local helper lemmas:
    - `array_contains_spec_hit`
    - `array_contains_spec_miss`
  - normalized shifted indices after `Znth_cons` with explicit `replace (j + 1 - 1) with j by lia`
  - corrected the equality orientation in the witness proofs with `symmetry`
  - made helper instantiation explicit with concrete arguments `l`, `k_pre`, and `i`
  - recovered `Zlength l = n_pre` in `return_wit_2` via `prop_apply IntArray.full_length`
  - fixed several proof-script bookkeeping mistakes caused by post-`entailer!` hypothesis renumbering
- Result:
  - `array_contains_proof_manual.v` compiled
  - `array_contains_goal_check.v` compiled
  - `array_contains_proof_manual.v` now contains no `Admitted.` and no added `Axiom`

## Final outcome

- `symexec` succeeded on the current annotated file.
- `array_contains_goal.v`, `array_contains_proof_auto.v`, `array_contains_proof_manual.v`, and `array_contains_goal_check.v` all compiled successfully.
- `proof_manual_grep.log` is empty, confirming no `Admitted.` or added `Axiom` remain in `array_contains_proof_manual.v`.
- Non-`.v` files under `coq/` were deleted after the successful compile replay.
