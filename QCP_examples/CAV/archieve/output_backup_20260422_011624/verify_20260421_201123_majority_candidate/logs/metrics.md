# Verify Metrics

## Verification Run

- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/majority_candidate.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/majority_candidate.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_201123_majority_candidate.c`
- Target function: `majority_candidate`

## Symexec

- symexec_start: `2026-04-21 20:14:12 +0800`
- symexec_end: `2026-04-21 20:14:12 +0800`
- symexec_elapsed: `<1 second`
- symexec_status: `0`
- symexec_result: `Successfully finished symbolic execution`

## Coq Compile

- Compile working directory: `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- Compiled original V: `original/majority_candidate.v`
- Compiled generated goal: `coq/generated/majority_candidate_goal.v`
- Compiled generated proof auto: `coq/generated/majority_candidate_proof_auto.v`
- Compiled generated proof manual: `coq/generated/majority_candidate_proof_manual.v`
- Compiled generated goal check: `coq/generated/majority_candidate_goal_check.v`
- goal_check_result: `passed`
- proof_manual_admitted: `none`
- proof_manual_new_axiom: `none`

## Cleanup

- Removed non-`.v` files under `coq/` after successful compile.
- Remaining non-`.v` files under `coq/`: `none`

## Experience

- Experience updates: none

Final Result: Success

## External Codex Run `20260421_201123`

- Start time: `2026-04-21 20:11:23 +0800`
- End time: `2026-04-21 20:20:02 +0800`
- Wall-clock time (seconds): `518.34`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `4992639`
- Codex CLI cached input tokens: `4867328`
- Codex CLI output tokens: `21307`
- Codex CLI total tokens: `5013946`
- Approx workspace-authored text tokens: `6175`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate/logs/codex_prompt_20260421_201123.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate/logs/codex_stdout_20260421_201123.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate/logs/codex_stderr_20260421_201123.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate/logs/codex_last_message_20260421_201123.txt`
