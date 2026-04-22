# Verify Metrics

## Workspace

- Workspace: `output/verify_20260420_233617_lower_bound`
- Input C: `input/lower_bound.c`
- Optional input V: none
- Target function: `lower_bound`
- Active annotated C: `annotated/verify_20260420_233617_lower_bound.c`

## Symexec

- Symexec start: `2026-04-20 23:36:xx +0800` approximately
- Symexec end: `2026-04-20 23:36:xx +0800` approximately
- Symexec elapsed: `2` seconds on the final successful run
- Symexec result: success
- Symexec log: `logs/qcp_run.log`
- Generated files:
  - `coq/generated/lower_bound_goal.v`
  - `coq/generated/lower_bound_proof_auto.v`
  - `coq/generated/lower_bound_proof_manual.v`
  - `coq/generated/lower_bound_goal_check.v`

## Proof And Compile

- Manual proof obligations completed: `6`
- Final compile replay working directory: `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- Compile result for `lower_bound_goal.v`: success
- Compile result for `lower_bound_proof_auto.v`: success
- Compile result for `lower_bound_proof_manual.v`: success
- Compile result for `lower_bound_goal_check.v`: success
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains user-added top-level `Axiom`: no
- `proof_auto.v` still contains generated `Admitted.` placeholders: yes
- Non-`.v` Coq intermediate files cleaned: yes

## Experience Updates

- Experience updates: none
- Reason: the execution rule for this task required working only inside the existing workspace.

Final Result: Success

## External Codex Run `20260420_233617`

- Start time: `2026-04-20 23:36:17 +0800`
- End time: `2026-04-20 23:50:30 +0800`
- Wall-clock time (seconds): `852.33`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `8369304`
- Codex CLI cached input tokens: `8199936`
- Codex CLI output tokens: `32745`
- Codex CLI total tokens: `8402049`
- Approx workspace-authored text tokens: `8547`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_233617_lower_bound/logs/codex_prompt_20260420_233617.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_233617_lower_bound/logs/codex_stdout_20260420_233617.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_233617_lower_bound/logs/codex_stderr_20260420_233617.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_233617_lower_bound/logs/codex_last_message_20260420_233617.txt`
