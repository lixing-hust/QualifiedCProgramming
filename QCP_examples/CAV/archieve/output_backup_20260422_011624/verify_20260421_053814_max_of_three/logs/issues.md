# Verify Issues

## Verification Outcome, 2026-04-21

- Phenomenon: the active annotated file for `max_of_three` had no extra Verify annotations beyond the input contract.
- Trigger condition: the function is scalar-only straight-line code with two `if` branches and no loops or heap ownership, so there was no loop head or heap-shape transition needing an `Inv`, bridge `Assert`, `which implies`, or loop-exit assertion.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_053814_max_of_three.c`, the two branch updates to local variable `m` and the final `return m`.
- Fix: no annotation edit was required. I ran `symexec` directly on the current active annotated C file and generated fresh `max_of_three_goal.v`, `max_of_three_proof_auto.v`, `max_of_three_proof_manual.v`, and `max_of_three_goal_check.v` in the current workspace.
- Result: `logs/qcp_run.log` ended with `Successfully finished symbolic execution` and `symexec_status: 0`.

## Manual Proof Check

- Phenomenon: manual proof work is only required when `coq/generated/max_of_three_proof_manual.v` contains generated theorem bodies or `Admitted.` placeholders.
- Trigger condition: after symbolic execution, the generated manual proof file contained imports only and no `proof_of_*` theorem to fill.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_053814_max_of_three/coq/generated/max_of_three_proof_manual.v`.
- Fix: no manual proof edit was made.
- Result: `max_of_three_proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.

## Full Compile And Cleanup

- Phenomenon: verification is not complete until `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile under the workspace logical path and Coq build intermediates are removed afterward.
- Trigger condition: normal completion rule for the Verify workflow.
- Localization: compile replay log `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_053814_max_of_three/logs/compile_full.log` and generated directory `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_053814_max_of_three/coq/generated/`.
- Fix: compiled the generated Coq files from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented load-path template, then removed non-`.v` files under the workspace `coq/` directory.
- Result: the full compile chain exited with `compile_status: 0`, `goal_check.v` compiled successfully, and `find coq -type f ! -name '*.v'` returned no files.
