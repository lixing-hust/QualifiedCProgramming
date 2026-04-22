# Metrics

## Verify Run

- Workspace: `output/verify_20260421_134943_house_robber`
- Target function: `house_robber`
- Input C: `input/house_robber.c`
- Input V: `input/house_robber.v`
- Active annotated C: `annotated/verify_20260421_134943_house_robber.c`

## Annotation

- Annotation changes required: yes
- Loop invariants added: 1
- Loop-exit assertions added: 0
- Bridge assertions added: 0
- Final annotation status: `symexec` succeeded on the current annotated file.

## Symexec

- symexec_start: `2026-04-21T13:52:57+08:00`
- symexec_end: `2026-04-21T13:52:58+08:00`
- symexec_elapsed: about `1s`
- symexec_status: `0`
- symexec_log: `logs/qcp_run.log`

## Proof

- Manual proof required: yes
- Manual obligations completed: 5
- Manual proof file: `coq/generated/house_robber_proof_manual.v`
- `Admitted.` in manual proof: none
- Top-level `Axiom` in manual proof: none

## Compile

- compile_start: `2026-04-21T14:05:14+08:00`
- compile_end: `2026-04-21T14:05:21+08:00`
- compile_elapsed: about `7s`
- Compiled original V: yes
- Compiled `goal.v`: yes
- Compiled `proof_auto.v`: yes
- Compiled `proof_manual.v`: yes
- Compiled `goal_check.v`: yes
- compile_log: `logs/compile.log`

## Cleanup

- Non-`.v` files under `coq/` cleaned: yes
- Remaining Coq files: generated `.v` files only

## Experience Updates

- Experience updates: none

Final Result: Success

## External Codex Run `20260421_134943`

- Start time: `2026-04-21 13:49:43 +0800`
- End time: `2026-04-21 14:07:07 +0800`
- Wall-clock time (seconds): `1043.87`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `12256311`
- Codex CLI cached input tokens: `12001792`
- Codex CLI output tokens: `40452`
- Codex CLI total tokens: `12296763`
- Approx workspace-authored text tokens: `7130`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_134943_house_robber/logs/codex_prompt_20260421_134943.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_134943_house_robber/logs/codex_stdout_20260421_134943.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_134943_house_robber/logs/codex_stderr_20260421_134943.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_134943_house_robber/logs/codex_last_message_20260421_134943.txt`
