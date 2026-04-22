# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Annotation layer

- Phenomenon: the initial annotated working copy had no loop invariant or exit assertion for the `for (i = 1; i <= n; ++i)` accumulation loop.
- Trigger: `sum_to_n` needs the accumulator to preserve a closed arithmetic summary across iterations; without that, `symexec` would not have a stable loop summary to generate useful witnesses from.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_153041_sum_to_n.c`
- Fix:
  - added an invariant recording `1 <= i <= n + 1`
  - preserved `n == n@pre`
  - summarized the processed prefix as `ret == (i - 1) * i / 2`
  - added a loop-exit assertion `i == n + 1` and `ret == n * (n + 1) / 2`
- Result: `symexec` succeeded and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Symexec invocation

- Phenomenon: this workspace initially had no generated Coq files, so the verification state depended on rerunning symbolic execution from scratch.
- Trigger: the active annotated file changed, and the verify skill requires a fresh `symexec` run after every annotation edit.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_153041_sum_to_n/logs/qcp_run.log`
- Fix:
  - cleared any stale generated files under `coq/generated/`
  - ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`
  - used the repository’s canonical flags:
    - `--input-file=<annotated.c>`
    - `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`
    - `--coq-logic-path=SimpleC.EE.CAV.verify_20260418_153041_sum_to_n`
    - `--no-exec-info`
- Result: `qcp_run.log` records successful symbolic execution into `sum_to_n`.

## Compile command quoting

- Phenomenon: the first manual compile launch failed before any proof checking.
- Trigger: the initial shell command used an overquoted chained command, which broke the `coqc` sequence.
- Localization: the first compile attempt from `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- Fix: rewrote the compile pass as a clean `set -e` bash script with an explicit `BASE=(...)` array and one `coqc` command per line.
- Result: later compile attempts reflected real proof-state failures instead of shell syntax noise.

## Manual proof iteration

- Phenomenon: the generated `sum_to_n_proof_manual.v` contained five `Admitted.` placeholders:
  - `proof_of_sum_to_n_safety_wit_3`
  - `proof_of_sum_to_n_safety_wit_4`
  - `proof_of_sum_to_n_entail_wit_1`
  - `proof_of_sum_to_n_entail_wit_2`
  - `proof_of_sum_to_n_entail_wit_3`
- Trigger: the loop invariant generated pure arithmetic witnesses that the auto proof did not discharge.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_153041_sum_to_n/coq/generated/sum_to_n_proof_manual.v`
- Fix chain:
  - started with the minimal `pre_process; entailer!; lia` skeleton
  - used `coqtop` to inspect the residual goals after `entailer!`
  - added local helper lemmas:
    - `tri_step`
    - `tri_nonneg`
    - `tri_monotone`
    - `tri_nonneg_inst`
  - proved the range obligation for `ret + i` by normalizing to the triangular closed form
  - proved the `i + 1` safety witness by deriving the concrete bound `n_pre <= 65535`
  - handled the exit witness by proving `i = n_pre + 1` and then rewriting the remaining equality
- Result: `sum_to_n_proof_manual.v` now compiles with no `Admitted.` and no user-added `Axiom`.

## Quotient notation mismatch

- Phenomenon: early arithmetic proof attempts failed with errors like:
  - `Found no subterm matching "... / ..."`
  - `Not convertible`
  - `Cannot find witness`
- Trigger: the generated notation `÷` is `Z.quot`, not `Z.div`, so direct use of `Z.div_*` lemmas did not match the goal terms.
- Localization: helper proofs inside `sum_to_n_proof_manual.v`
- Fix:
  - confirmed the notation with `Locate "÷"`
  - used `Z.quot_div_nonneg` in nonnegative branches to bridge into `Z.div`
  - used the quotient-aware monotonicity/positivity facts through that bridge
- Result: the arithmetic helper lemmas became stable and reusable inside the witness proofs.

## Older Coq parser / tactic-shape compatibility

- Phenomenon: several proof scripts failed with parser-state or empty-goal issues:
  - `Syntax error: ']' expected after [for_each_goal]`
  - `No such goal`
- Trigger:
  - compact tactical forms like `split; [ ... | ]` were rejected in this proof context
  - some witnesses were fully solved by `pre_process` or `entailer!`, so trailing tactics ran on an empty proof state
- Localization: `sum_to_n_proof_manual.v`
- Fix:
  - rewrote proofs in the conservative style:
    - explicit bullets instead of compact bracketed forms
    - explicit rewrites instead of large tactical one-liners
    - removed redundant `entailer!` where `pre_process` had already closed the goal
- Result: the final proof script is accepted by the current Coq environment.

## Numeric contradiction shape after `vm_compute`

- Phenomenon: the contradiction used to rule out `n_pre > 65535` did not reduce to a direct arithmetic inequality after `vm_compute`.
- Trigger: the computed proof object normalized to a contradiction witness rather than a plain numeric comparison.
- Localization: `proof_of_sum_to_n_safety_wit_4`
- Fix:
  - converted the contradiction by:
    - `pose proof (Z.le_trans _ _ _ Hmono H5) as Hcontra`
    - `vm_compute in Hcontra`
    - `exfalso; apply Hcontra; reflexivity`
- Result: the branch now closes deterministically.

## Final outcome

- `symexec` succeeded on the current annotated file.
- `sum_to_n_goal.v`, `sum_to_n_proof_auto.v`, `sum_to_n_proof_manual.v`, and `sum_to_n_goal_check.v` all compiled successfully.
- `sum_to_n_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the successful compile pass.
