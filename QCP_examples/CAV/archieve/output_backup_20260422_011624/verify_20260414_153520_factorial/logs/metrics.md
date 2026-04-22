# Verify Metrics

## Verify Run `20260414_153520`

- Stage: `verify`
- Status: `completed_with_manual_recovery`
- Start time: `2026-04-14 15:35:20 +0800`
- End time: `2026-04-14 16:01:43 +0800`
- Total wall-clock time (seconds): `1583.00`
- Token source: exact Codex CLI usage unavailable because the external verify driver was terminated during manual recovery.
- Approx prompt tokens: unavailable
- Approx final-message tokens: unavailable
- External Codex workspace generation:
  - Produced `annotated/factorial.c`
  - Produced `logs/annotation_reasoning.md`
  - Produced `logs/proof_reasoning.md`
  - Produced `coq/generated/factorial_goal.v`
  - Produced `coq/generated/factorial_proof_auto.v`
  - Produced `coq/generated/factorial_proof_manual.v`
  - Produced `coq/generated/factorial_goal_check.v`
- Manual recovery steps:
  - Fixed `coq/generated/factorial_proof_manual.v`
  - Recompiled `factorial_goal.v`
  - Recompiled `factorial_proof_auto.v`
  - Recompiled `factorial_proof_manual.v`
  - Recompiled `factorial_goal_check.v`
- Final result:
  - `coq/generated/factorial_proof_manual.v` compiles without `Admitted.` or `Axiom`
  - `coq/generated/factorial_goal_check.v` compiles successfully
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/output/verify_20260414_153520_factorial/logs/codex_prompt_20260414_153520.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/output/verify_20260414_153520_factorial/logs/codex_stdout_20260414_153520.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/output/verify_20260414_153520_factorial/logs/codex_stderr_20260414_153520.log`
