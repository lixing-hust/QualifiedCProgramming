# Verification Issues

## Summary

- Status: incomplete
- Symexec on the current annotated file: passed
- Manual proof: incomplete
- Final compile chain: blocked at `array_replace_k_proof_manual.v`
- `goal_check.v`: not compiled successfully end to end

## Issue 1: loop-body bridge annotations crashed the verifier frontend

- Phenomenon:
  - the first annotated reruns of `symexec` exited with a segmentation fault and produced empty generated Coq files
- Trigger condition:
  - the active annotated copy used richer loop-body bridge assertions for the `if (a[i] == old_k)` branch join
- Localization:
  - `annotated/verify_20260418_192950_array_replace_k.c`
  - `logs/qcp_run.log`
- Diagnosis:
  - a control run on the original input produced the expected verifier error `Lack of assertions in some paths for the loop!`
  - so the toolchain itself was healthy on this function, and the crash came from the richer bridge syntax rather than from `array_replace_k` as a program shape
- Fix:
  - reduced the active annotated file to the loop invariant only
  - removed the loop-body bridge assertions that caused the frontend crash
- Result:
  - `symexec` completed successfully on the reduced annotated file
  - fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` were generated

## Issue 2: the generated manual proof needed iterative Coq-version cleanup

- Phenomenon:
  - the first `coqc` pass for `array_replace_k_proof_manual.v` failed before semantic proof checking
- Trigger condition:
  - the initial scripts used syntax forms that are not stable in this environment:
    - combined `Exists x, y`
    - newer `induction ... as [...]`
- Localization:
  - `coq/generated/array_replace_k_proof_manual.v`
  - `logs/compile_proof_manual.log`
- Diagnosis:
  - this Coq environment expects the older proof style already used in other repository examples
- Fix chain:
  - split combined witnesses into one `Exists ... .` per witness
  - rewrote the local helper lemma to use older proof structure:
    - `induction l1.`
    - `destruct l2.`
    - plain `IHl1`
  - replaced the unavailable lemma name `Zlength_eq` with a local extensionality lemma `list_eq_by_Znth`
- Result:
  - the proof advanced beyond parser-level failures and into the actual list-rewrite obligations

## Issue 3: `entail_wit_2_1` remained blocked in list-splitting proof details

- Phenomenon:
  - compile-driven proof iteration repeatedly progressed but stopped inside the proof of `Hl2` and later branch-specific rewrites in `proof_of_array_replace_k_entail_wit_2_1`
- Trigger condition:
  - the proof reconstructs `l2_2 = sublist i n_pre l` and then rewrites `replace_Znth` over a prefix/suffix split
- Localization:
  - `coq/generated/array_replace_k_proof_manual.v`
  - `logs/compile_proof_manual.log`
- Diagnosis:
  - several small but real proof-shape mismatches had to be corrected one by one:
    - impossible `cons` versus `nil` branch needed explicit `Zlength_nil` / `Zlength_cons`
    - `Znth_cons` only applies for positive indices, so the head case had to use `simpl`
    - the tail case needed `replace (k + 1 - 1) with k by lia`
    - the split proof needed `Zlength_sublist`, not `Zlength_sublist0`
    - the suffix proof needed `replace (k + i) with (i + k) by lia`
    - hardcoded generated hypothesis numbers were unstable and had to be replaced with `match goal` patterns
- Fix attempts:
  - updated the helper lemma and branch proofs through multiple compile iterations
  - replaced brittle numbered hypotheses with formula-shaped `match goal`
  - normalized the arithmetic and list-index expressions step by step
- Result:
  - the proof got materially further than the initial draft
  - verification still remains blocked because `array_replace_k_proof_manual.v` does not compile yet

## Issue 4: final verification status is still fail

- Phenomenon:
  - the current workspace does not satisfy the verify completion criteria
- Trigger condition:
  - `array_replace_k_proof_manual.v` is not yet compiled successfully
  - `array_replace_k_goal_check.v` therefore has not been compiled successfully end to end
- Diagnosis:
  - the remaining work is in the manual proof layer, not in annotation design or symbolic execution
- Fix:
  - none yet in this turn
- Result:
  - final status remains `Fail`

## Trace Files

- Symexec log:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_192950_array_replace_k/logs/qcp_run.log`
- Compile logs:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_192950_array_replace_k/logs/compile_goal.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_192950_array_replace_k/logs/compile_proof_auto.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_192950_array_replace_k/logs/compile_proof_manual.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_192950_array_replace_k/logs/compile_goal_check.log`
