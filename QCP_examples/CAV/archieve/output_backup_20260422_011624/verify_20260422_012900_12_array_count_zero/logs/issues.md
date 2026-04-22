# Verification Issues

## Summary

- `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`; it was updated early using only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- The original annotated C file had no loop invariant, so the verifier had no relation between `count` and the processed prefix of `l`.
- `symexec` succeeded after adding a prefix-count invariant and loop-exit assertion to `annotated/verify_20260419_235425_array_count_zero.c`.
- The generated manual proof required helper lemmas for `array_count_zero_spec` over appended singletons and count bounds over prefixes.
- Final status:
  - `array_count_zero_goal.v` compiled
  - `array_count_zero_proof_auto.v` compiled
  - `array_count_zero_proof_manual.v` compiled
  - `array_count_zero_goal_check.v` compiled
  - `array_count_zero_proof_manual.v` contains no `Admitted.` and no added `Axiom`
  - non-`.v` files under `coq/` were removed

## Issue 1: Missing prefix-count loop invariant

- Symptom:
  - the initial active annotated C file was identical to the input C file and had no `Inv` or loop-exit `Assert`
- Trigger condition:
  - the implementation counts zero elements with a `for` loop, while the postcondition is stated over the full logical list `l`
- Diagnosis:
  - without a loop invariant, the verifier cannot preserve that `count` equals `array_count_zero_spec` over the processed prefix
  - the closest verified pattern is the `count_equal_to_k` example, specialized here to `k = 0`
- Fix:
  - added invariant `count == array_count_zero_spec(sublist(0, i, l))`
  - preserved `a == a@pre`, `n == n@pre`, index bounds, and `IntArray::full(a, n, l)`
  - added a loop-exit assertion fixing `i == n` and `count == array_count_zero_spec(l)`
- Result:
  - `symexec` completed successfully and generated fresh Coq obligations for the current annotated file

## Issue 2: Manual proof needed list-extension helper lemmas

- Symptom:
  - `array_count_zero_proof_manual.v` was generated with five admitted lemmas:
    `safety_wit_4`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `entail_wit_3`
- Trigger condition:
  - loop preservation needs to relate `sublist 0 (i + 1) l` to `sublist 0 i l ++ [Znth i l 0]`
- Diagnosis:
  - direct automation did not know how to rewrite `array_count_zero_spec` over an appended singleton
  - the overflow witness also needed an explicit upper bound on the prefix count
- Fix:
  - added `array_count_zero_spec_app_single`
  - added `array_count_zero_spec_bounds`
  - used `sublist_split`, `sublist_single`, branch facts from `Z.eq_dec`, and `store_int_range (&("n")) n_pre`
- Result:
  - the manual proof compiled and contains no remaining `Admitted.`

## Trace Files

- Symexec log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_235425_array_count_zero/logs/qcp_run.log`
- Compile log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_235425_array_count_zero/logs/compile_full.log`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `1`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_235425_array_count_zero/logs/codex_stderr_20260419_235425.log`
