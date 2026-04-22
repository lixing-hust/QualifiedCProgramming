# Verify Issues

## Initial fingerprint placeholders

- Phenomenon: `logs/workspace_fingerprint.json` still had an empty `semantic_description` and empty `keywords` at task start.
- Trigger: workspace had only the initialized logs and original C snapshot.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read the controlled vocabulary in `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and controlled keywords for an array/pointer `for_loop` with loop-invariant, heap-reasoning, range-bound, overflow-guard, and empty-loop behavior.
- Result: the fingerprint is valid JSON and no longer contains empty semantic placeholders.

## Missing loop invariant for output prefix

- Phenomenon: the active annotated C had no loop invariant for `for (i = 0; i < n; ++i)`, so symbolic execution would not have a stable summary for the partially written `out` buffer.
- Trigger: `array_negate` writes `out[i]` one element at a time while the postcondition requires a complete result list `lr` satisfying `lr[i] == -la[i]`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260419_234634_array_negate.c`, loop before `out[i] = -a[i];`.
- Fix: added an invariant with witnesses `l1` and `l2`, where `l1` is the processed negated prefix, `l2` is the original `lo` suffix, and the heap is `IntArray::full(out, n@pre, app(l1, l2))` while preserving `a`, `out`, and `n` as pre-state parameters.
- Result: the next clean `symexec` run generated fresh `array_negate_goal.v`, `array_negate_proof_auto.v`, `array_negate_proof_manual.v`, and `array_negate_goal_check.v`.

## Contract binder parser syntax

- Phenomenon: existing CAV examples and issue logs show the frontend rejects comma-separated contract binders with `unexpected PT_COMMA, expecting PT_REQUIRE`.
- Trigger: the active annotated copy inherited `/*@ With la, lo` from the input contract.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260419_234634_array_negate.c`, function contract binder line.
- Fix: changed only the active annotated copy to `With la lo`, leaving the `Require` and `Ensure` formulas unchanged and not modifying `input/array_negate.c`.
- Result: `symexec` parsed the function and completed symbolic execution successfully.

## Manual proof obligations

- Phenomenon: after successful `symexec`, `coq/generated/array_negate_proof_manual.v` contained four `Admitted.` obligations: `safety_wit_2`, `entail_wit_1`, `entail_wit_2`, and `return_wit_1`.
- Trigger: the generated VCs require pure arithmetic/list reasoning for unary negation safety, prefix/suffix invariant initialization, loop preservation after `replace_Znth`, and final suffix elimination.
- Localization: `coq/generated/array_negate_proof_manual.v`.
- Fix: adapted the verified `array_scale` proof pattern to unary negation. The safety proof instantiates the contract overflow guard at the loop index; the initialization proof chooses `l2 = lo` and `l1 = nil`; the preservation proof rewrites the output update into `l1 ++ [-la[i]] ++ sublist(i + 1, n, lo)`; the return proof derives `i = n`, proves `l2 = nil`, and chooses `lr = l1`.
- Result: `array_negate_proof_manual.v` compiled and contains no remaining `Admitted.` or newly defined `Axiom`.

## Full compile replay and cleanup

- Phenomenon: verification cannot be considered complete until `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile with the workspace-specific logical prefix.
- Trigger: the workspace generated files import `SimpleC.EE.CAV.verify_20260419_234634_array_negate`.
- Localization: compile logs `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, and `logs/compile_goal_check.log`.
- Fix: ran `coqc` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the `_CoqProject`-style base `-R` paths and `-R coq/generated SimpleC.EE.CAV.verify_20260419_234634_array_negate`; reused the public strategy `.vo` files under `SeparationLogic/examples`.
- Result: all four compile steps passed, all compile logs are empty, and non-`.v` files under `coq/` were deleted after the successful replay.
