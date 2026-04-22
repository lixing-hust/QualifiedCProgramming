# Verify Issues

## Contract Binder Parser Syntax

- Phenomenon: the first manual `symexec` run failed before VC generation.
- Trigger: the active annotated copy inherited `/*@ With la, lo`, and the frontend reported `syntax error, unexpected PT_COMMA, expecting PT_REQUIRE` at `annotated/verify_20260419_233300_array_scale.c:6:12`.
- Localization: active annotated C contract binder line; repository examples use space-separated binders such as `With la lb lo`.
- Fix: changed only the active annotated copy to `With la lo`, leaving the `Require` and `Ensure` formulas unchanged.
- Result: the next `symexec` run parsed the function and reached symbolic execution of the loop body.

## Over-Specified Bridge Assertions Dropped Scalar Locals

- Phenomenon: the second `symexec` run failed at the post-assignment `which implies` near line 63 of the active annotated file.
- Trigger: the loop-body bridge assertions manually opened `a[i]` and `out[i]` but did not preserve stack permissions for scalar locals `n` and `k`.
- Evidence: `logs/qcp_run.log` showed the stored output value as `la[i] * NULL` and reported unsolved SEP entries for `store(n_93_addr, ...)` and `store(k_87_addr, ...)`.
- Localization: active annotated C loop-body bridge assertions around `out[i] = a[i] * k`.
- Fix: removed both bridge assertions and kept the prefix/tail loop invariant only, matching existing scalar-key examples that let array strategies handle simple indexed reads/writes.
- Result: `symexec` succeeded and generated fresh `array_scale_goal.v`, `array_scale_proof_auto.v`, `array_scale_proof_manual.v`, and `array_scale_goal_check.v`.

## Generated Coq Logical Path Alignment

- Phenomenon: the first successful `symexec` used `--coq-logic-path=SimpleC.EE`, producing generated imports inconsistent with the workspace compile template.
- Trigger: compile workflow expects generated files under `SimpleC.EE.CAV.verify_20260419_233300_array_scale`.
- Localization: generated `array_scale_proof_manual.v` and `array_scale_goal_check.v` import lines.
- Fix: reran `symexec` with `--coq-logic-path=SimpleC.EE.CAV.verify_20260419_233300_array_scale`, then reapplied the manual proofs to the regenerated `proof_manual.v`.
- Result: generated imports matched the expected workspace-specific logical prefix.

## Coq Load Path Invocation Directory

- Phenomenon: the first full compile attempt failed on `array_scale_goal.v` with `Cannot find a physical path bound to logical path int_auto with prefix AUXLib`.
- Trigger: `coqc` was invoked from `/home/yangfp/QualifiedCProgramming`, while the `_CoqProject` paths used by this repository are relative to `/home/yangfp/QualifiedCProgramming/SeparationLogic`.
- Localization: `logs/compile_goal.log`.
- Fix: reran the compile sequence from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the same base `-R` paths and workspace `-R` path.
- Result: `array_scale_goal.v` and `array_scale_proof_auto.v` compiled successfully.

## Manual Proof Goal Order and Hypothesis Numbering

- Phenomenon: `array_scale_proof_manual.v` initially failed in `array_scale_entail_wit_2` with `Cannot find witness`.
- Trigger: after `entailer!`, the generated pure subgoals were ordered as suffix element relation, prefix element relation, suffix length, and prefix length, but the first proof script handled the prefix relation first.
- Localization: `array_scale_proof_manual.v`, `proof_of_array_scale_entail_wit_2`.
- Fix: inspected the proof state in `coqtop`, then reordered the bullets and proved the suffix relation with `Znth_sublist`.
- Result: `array_scale_entail_wit_2` compiled.

- Phenomenon: the next compile failed in `array_scale_return_wit_1` because the proof script referenced the old `array_add` hypothesis numbering.
- Trigger: in this generated goal, `H5` is the suffix length equality and `H6` is the prefix semantic relation.
- Localization: `array_scale_proof_manual.v`, `proof_of_array_scale_return_wit_1`.
- Fix: rewrote `Zlength_cons` in `H5`, used `H6` for the final element relation, and rewrote the range with `H12 : Zlength l1 = n_pre`.
- Result: `array_scale_proof_manual.v` compiled, and then `array_scale_goal_check.v` compiled.

## Final Outcome

- Latest `symexec` succeeded on the current active annotated file.
- Full compile replay succeeded for `array_scale_goal.v`, `array_scale_proof_auto.v`, `array_scale_proof_manual.v`, and `array_scale_goal_check.v`.
- `array_scale_proof_manual.v` contains no `Admitted.` and no new `Axiom`.
- Non-`.v` files under the workspace `coq/` directory were deleted after the successful compile pass.
