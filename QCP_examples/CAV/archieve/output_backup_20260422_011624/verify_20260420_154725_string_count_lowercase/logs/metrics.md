# Verify Metrics

## Workspace

- Workspace: `output/verify_20260420_154725_string_count_lowercase`
- Input C: `input/string_count_lowercase.c`
- Input V: `input/string_count_lowercase.v`
- Active annotated C: `annotated/verify_20260420_154725_string_count_lowercase.c`
- Target function: `string_count_lowercase`

## Symexec

- symexec_start: `2026-04-20T15:50:01+08:00`
- symexec_end: `2026-04-20T15:50:01+08:00`
- symexec_elapsed: `<1 second`
- symexec_status: `0`
- symexec_log: `logs/qcp_run.log`

## Annotation

- Added loop invariant: yes
- Added loop-exit assertion: yes
- Final invariant shape: `exists l1 l2`, with `l == app(l1, l2)`, `Zlength(l1) == i`, and `cnt == string_count_lowercase_spec(l1)`.

## Proof

- Manual proof obligations generated: `6`
- Manual proof obligations completed: `6`
- Helper lemmas added in `proof_manual.v`: `2`
- `proof_manual.v` contains `Admitted.`: `no`
- `proof_manual.v` contains top-level `Axiom`: `no`

## Compile

- compile_start: `2026-04-20T15:56:47+08:00`
- compile_end: `2026-04-20T15:56:52+08:00`
- compile_elapsed: `5 seconds`
- compile_log: `logs/compile_all.log`
- compiled_original_v: `success`
- compiled_goal_v: `success`
- compiled_proof_auto_v: `success`
- compiled_proof_manual_v: `success`
- compiled_goal_check_v: `success`

## Cleanup

- Removed non-`.v` files under `coq/`: `yes`
- Remaining non-`.v` files under `coq/`: `0`

## Experience

- Experience updates: none

Final Result: Success

## External Codex Run `20260420_154725`

- Start time: `2026-04-20 15:47:25 +0800`
- End time: `2026-04-20 15:58:16 +0800`
- Wall-clock time (seconds): `650.75`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `4982088`
- Codex CLI cached input tokens: `4828544`
- Codex CLI output tokens: `26128`
- Codex CLI total tokens: `5008216`
- Approx workspace-authored text tokens: `7790`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154725_string_count_lowercase/logs/codex_prompt_20260420_154725.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154725_string_count_lowercase/logs/codex_stdout_20260420_154725.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154725_string_count_lowercase/logs/codex_stderr_20260420_154725.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_154725_string_count_lowercase/logs/codex_last_message_20260420_154725.txt`
