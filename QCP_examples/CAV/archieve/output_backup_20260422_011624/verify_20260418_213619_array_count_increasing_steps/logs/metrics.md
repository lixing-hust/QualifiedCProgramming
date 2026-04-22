# Metrics

- Workspace: `verify_20260418_213619_array_count_increasing_steps`
- Target function: `array_count_increasing_steps`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_count_increasing_steps.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_count_increasing_steps.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_213619_array_count_increasing_steps.c`
- Symexec status: success on current annotated file
- Workspace-local dependency shim used: `coq/deps/array_count_increasing_steps.v`
- Compile replay status:
  - `coq/deps/array_count_increasing_steps.v`: pass
  - `original/array_count_increasing_steps.v`: expected fail, preserved as read-only input; workspace compile uses the local shim instead
  - `array_count_increasing_steps_goal.v`: pass
  - `array_count_increasing_steps_proof_auto.v`: pass
  - `array_count_increasing_steps_proof_manual.v`: pass
  - `array_count_increasing_steps_goal_check.v`: pass
- Manual proof status:
  - no `Admitted.` in `coq/generated/array_count_increasing_steps_proof_manual.v`
  - no user-added `Axiom` in `coq/generated/array_count_increasing_steps_proof_manual.v`
- Cleanup status:
  - compile replay executed
  - non-`.v` files under `coq/generated/` and `coq/deps/` cleaned after validation
- Experience updates: none

Final Result: Success
