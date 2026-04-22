# Verify Metrics

- Workspace: `verify_20260420_174025_array_sign`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_sign.c`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_174025_array_sign.c`
- Target function: `array_sign`

## Symexec Attempts

- Initial parser attempt: failed immediately on `With la, lo` comma syntax.
- Invariant-only attempt after binder normalization: stopped after no progress and zero-byte generated files.
- Branch-local bridge attempt: failed at a partial implication carrying local `n` stack resource.
- In-body `n` removal attempt: stopped after no progress and zero-byte generated files.
- Single-write source normalization attempt: failed because scalar `s` was dropped before `out[i] = s`.
- Scalar-preserving bridge attempt: failed at a partial implication carrying local `a` stack resource.
- Pre-state pointer bridge attempt: `symexec` segfaulted after clause explosion, exit 139.
- Disjunctive sign-relation attempt: rejected by frontend with `Multiple cases inside pre- or post-condition`.

## Generated Artifacts

- Successful symexec: no
- Generated Coq files: none retained; zero-byte failed outputs were removed
- Coq compile attempted: no, because symexec never produced valid generated files
- Manual proof attempted: no, because `proof_manual.v` was not generated
- Non-`.v` Coq intermediates cleaned: yes; none were present

Experience updates: none
Final Result: Fail

## External Codex Run `20260420_174025`

- Start time: `2026-04-20 17:40:25 +0800`
- End time: `2026-04-20 18:10:06 +0800`
- Wall-clock time (seconds): `1780.99`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `7295456`
- Codex CLI cached input tokens: `7024128`
- Codex CLI output tokens: `31052`
- Codex CLI total tokens: `7326508`
- Approx workspace-authored text tokens: `2832`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_prompt_20260420_174025.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_stdout_20260420_174025.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_stderr_20260420_174025.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_last_message_20260420_174025.txt`

## Retry Completion `2026-04-20 18:18:52 CST`

- Continued workspace: `verify_20260420_174025_array_sign`
- Current annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_174025_array_sign.c`
- Current generated directory: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/coq/generated`

### Retry Symexec Attempts

- Helper-based invariant with `sign_list`: failed immediately with `symexec` segfault before normal startup output.
- Scalar-helper invariant with `sign_value`: failed immediately with `symexec` segfault before normal startup output.
- Native split-implication invariant: succeeded.
- Successful symexec start: `2026-04-20 18:16:27 CST`
- Successful symexec end: `2026-04-20 18:16:27 CST`
- Successful symexec elapsed: `0s`

### Retry Generated Artifacts

- Generated `array_sign_goal.v`: yes
- Generated `array_sign_proof_auto.v`: yes
- Generated `array_sign_proof_manual.v`: yes
- Generated `array_sign_goal_check.v`: yes
- Manual proof obligations: `proof_of_array_sign_entail_wit_1`
- Manual proof completed: yes
- `proof_manual.v` contains `Admitted.`: no
- `proof_manual.v` added `Axiom`: no

### Retry Compile Results

- `array_sign_goal.v`: pass
- `array_sign_proof_auto.v`: pass
- `array_sign_proof_manual.v`: pass
- `array_sign_goal_check.v`: pass
- Compile logs: `logs/compile_goal.log`, `logs/compile_proof_auto.log`, `logs/compile_proof_manual.log`, `logs/compile_goal_check.log`
- Non-`.v` Coq intermediates cleaned: yes

Experience updates:
- `doc/experiences/ASSERTION.md`
- `doc/experiences/SYMEXEC.md`
Final Result: Success

## External Codex Run `20260420_181006`

- Start time: `2026-04-20 18:10:06 +0800`
- End time: `2026-04-20 18:19:51 +0800`
- Wall-clock time (seconds): `584.93`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `5576748`
- Codex CLI cached input tokens: `5430528`
- Codex CLI output tokens: `25378`
- Codex CLI total tokens: `5602126`
- Approx workspace-authored text tokens: `5024`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_prompt_20260420_181006.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_stdout_20260420_181006.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_stderr_20260420_181006.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_174025_array_sign/logs/codex_last_message_20260420_181006.txt`
