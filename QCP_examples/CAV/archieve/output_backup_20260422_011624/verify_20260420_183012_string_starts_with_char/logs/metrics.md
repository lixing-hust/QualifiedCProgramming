# Verify Metrics

## Workspace

- Workspace: `output/verify_20260420_183012_string_starts_with_char`
- Input C: `input/string_starts_with_char.c`
- Optional input V: none
- Active annotated C: `annotated/verify_20260420_183012_string_starts_with_char.c`
- Target function: `string_starts_with_char`

## Symexec

- symexec_start: `2026-04-20 18:31:26 +0800`
- symexec_end: `2026-04-20 18:31:26 +0800`
- symexec_elapsed: `<1s`
- symexec_log: `logs/qcp_run.log`
- symexec_result: success

## Annotation

- Annotation edits required: no
- Annotation reasoning log: skipped because no `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion was needed.

## Proof

- Manual proof edits required: yes
- Manual witnesses completed:
  - `proof_of_string_starts_with_char_return_wit_1`
  - `proof_of_string_starts_with_char_return_wit_2`
  - `proof_of_string_starts_with_char_return_wit_3`
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` contains newly added `Axiom`: no

## Compile

- `string_starts_with_char_goal.v`: passed
- `string_starts_with_char_proof_auto.v`: passed
- `string_starts_with_char_proof_manual.v`: passed
- `string_starts_with_char_goal_check.v`: passed
- Original task `.v`: not present, skipped

## Cleanup

- Removed non-`.v` Coq byproducts under workspace `coq/`: yes

## Experience Updates

- Experience updates: none

Final Result: Success

## External Codex Run `20260420_183012`

- Start time: `2026-04-20 18:30:12 +0800`
- End time: `2026-04-20 18:36:42 +0800`
- Wall-clock time (seconds): `390.26`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `3035245`
- Codex CLI cached input tokens: `2878336`
- Codex CLI output tokens: `15259`
- Codex CLI total tokens: `3050504`
- Approx workspace-authored text tokens: `3476`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183012_string_starts_with_char/logs/codex_prompt_20260420_183012.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183012_string_starts_with_char/logs/codex_stdout_20260420_183012.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183012_string_starts_with_char/logs/codex_stderr_20260420_183012.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_183012_string_starts_with_char/logs/codex_last_message_20260420_183012.txt`
