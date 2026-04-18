# Verification Issues

## Summary

- `symexec` succeeded after adding the prefix-count invariant and loop-exit assertion to the annotated C file.
- A second annotation iteration was required because the first invariant omitted the unchanged-parameter fact `k == k@pre`.
- After regenerating the witnesses with that equality preserved, all remaining obligations were discharged in `count_equal_to_k_proof_manual.v`.
- Final status:
  - `count_equal_to_k_goal.v` compiled
  - `count_equal_to_k_proof_auto.v` compiled
  - `count_equal_to_k_proof_manual.v` compiled
  - `count_equal_to_k_goal_check.v` compiled
  - `count_equal_to_k_proof_manual.v` contains no `Admitted.` and no added `Axiom`
  - non-`.v` files under `coq/` were removed

## Issue 1: Missing unchanged-parameter relation for `k`

- Symptom:
  - the first manual-proof attempt got stuck at the return witness layer
  - the generated obligations still distinguished current `k` from `k_pre`
- Trigger condition:
  - the first loop invariant preserved `a == a@pre` and `n == n@pre` but not `k == k@pre`
- Diagnosis:
  - the compile-driven proof iteration showed that `return_wit_1` needed to rewrite the result from `count_equal_to_k_spec(l, k)` to `count_equal_to_k_spec(l, k_pre)`
  - this matched the repository guidance that unchanged parameters should be preserved in the annotation layer rather than reconstructed in manual proof
- Fix:
  - strengthen the loop invariant with `k == k@pre`
  - strengthen the loop-exit assertion with `k == k@pre`
  - clear generated Coq files and rerun `symexec`
- Result:
  - regenerated witnesses mention only `k_pre` where needed
  - the old return-witness blocker disappeared

## Issue 2: Safety witness needed explicit `store_int_range` on `n`

- Symptom:
  - `proof_of_count_equal_to_k_safety_wit_3` remained incomplete after a direct `entailer!`
- Trigger condition:
  - the proof needed an explicit upper bound strong enough to show `ret + 1 <= INT_MAX`
- Diagnosis:
  - a temporary debug proof file showed the residual goal was the overflow bound on `ret + 1`
  - proving only `0 <= ret <= i` from the prefix-count spec was not enough; the proof also needed the stored integer bound on `n_pre`
- Fix:
  - switch this witness to `pre_process`
  - use `store_int_range (&("n")) n_pre`
  - combine that range with `0 <= ret <= i` and `i < n_pre`, then finish with `entailer!`
- Result:
  - the safety witness compiled cleanly

## Issue 3: Several witness scripts initially overran finished goals

- Symptom:
  - compile errors such as `No such goal` appeared in manual proof
- Trigger condition:
  - some generated witnesses were already solved by `entailer!` or by the final branch simplification
- Diagnosis:
  - `entail_wit_1` needed no extra rewriting after `entailer!`
  - `entail_wit_2_1` finished after simplifying the `Z.eq_dec k_pre k_pre` branch
- Fix:
  - trim the proofs back to the minimum steps actually required by the regenerated goal shape
- Result:
  - the remaining proof file became short and stable

## Trace Files

- Symexec log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/qcp_run.log`
- Compile logs:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/compile_original.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/compile_goal.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/compile_proof_auto.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/compile_proof_manual.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_021719_count_equal_to_k/logs/compile_goal_check.log`
