## 2026-04-20 symexec parser issue

- Phenomenon: first symexec run failed before VC generation with `unexpected PT_COMMA, expecting PT_REQUIRE` at line 6 of the annotated file.
- Trigger: the active annotated copy inherited `With la, lb, lo`, and this front end rejects comma-separated binder lists.
- Localization: /home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_182127_array_pairwise_sum.c:6.
- Fix action: normalize only the annotated working copy to `With la lb lo`; leave Require and Ensure unchanged.

## 2026-04-20 symexec logical path correction

- Phenomenon: the first successful symexec run used `--coq-logic-path=SimpleC.EE.CAV.output.verify_20260420_182127_array_pairwise_sum.coq.generated`, causing generated imports to include `.output...coq.generated` instead of the documented workspace prefix.
- Trigger: manual symexec invocation used the physical workspace path shape rather than the compile-template logical prefix.
- Localization: generated `array_pairwise_sum_proof_manual.v` import line before regeneration.
- Fix action: clear generated Coq files and rerun symexec with `--coq-logic-path=SimpleC.EE.CAV.verify_20260420_182127_array_pairwise_sum` before compiling.

## 2026-04-20 manual proof obligations

- Phenomenon: generated `array_pairwise_sum_proof_manual.v` contained six `Admitted.` placeholders after successful symbolic execution.
- Trigger: the prefix/suffix loop invariant and bridge assertions produced explicit overflow, invariant packaging, return, and `which implies` witnesses that the auto proof did not discharge.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_182127_array_pairwise_sum/coq/generated/array_pairwise_sum_proof_manual.v`.
- Fix action: adapted the completed `array_add` proof pattern to the current function, proving the overflow witness from the contract hypothesis, packaging the loop invariant existentials, deriving the empty suffix at loop exit, splitting and merging array cells with `IntArray` lemmas, and normalizing the updated output list in the second `which implies` witness.
- Result: `array_pairwise_sum_proof_manual.v` compiled with no `Admitted.` and no top-level `Axiom`.

## 2026-04-20 final compile and cleanup

- Phenomenon: verification required full replay, not just successful `symexec`.
- Trigger: the workflow completion rule requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile under the documented load path.
- Localization: generated files under `coq/generated/`.
- Fix action: compiled all four generated Coq files from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths plus `-Q original ""` and `-R coq/generated SimpleC.EE.CAV.verify_20260420_182127_array_pairwise_sum`; then deleted all non-`.v` files under `coq/`.
- Result: `array_pairwise_sum_goal_check.v` compiled successfully and `find coq -type f ! -name '*.v'` returned no files.
