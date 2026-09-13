# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `callee-error-returns`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Helpers: prohibited because this case has no active case lib


### `proof_of_grant_cspace_cap_return_wit_7_callee_null` — `LLM_pre_process`

Strategy: Select the running-zero, null-target, class-valid disjunct; derive running = 0 from the zero low-32-bit premise and byte-valued OSRunning ownership, normalize the destination table and CapParent indices, and cancel the full frame.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_grant_cspace_cap_return_wit_8_callee_invalid` — `LLM_pre_process`

Strategy: Select the running-zero, class-invalid disjunct; derive running = 0 from the zero low-32-bit premise and byte-valued OSRunning ownership, then cancel the scheduler and CapParent frame after index normalization.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

## Write boundary

- Editable top-level proof spans: `proof_of_grant_cspace_cap_return_wit_7_callee_null`, `proof_of_grant_cspace_cap_return_wit_8_callee_invalid`.
- Editable aggressive split-goal proof spans: none.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- This case has no active case lib. Edit only the assigned manual proof spans; do not add helpers, imports, or another formal file.
- All declaration statements, other proof tokens, and the manual prelude stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/home/lixing/projects/QualifiedCProgramming/verification_runs/grant_cspace_cap-20260913165358/grant_cspace_cap-vc-proving-r1/groups/group_03__callee-error-returns/grant_cspace_cap_proof_manual.v`
- Active case lib: none; no `group_worker_lib` exists for this group
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/rounds/grant_cspace_cap-vc-proving-r1/groups/group_03__callee-error-returns/group_worker_report.json`
- Notes: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/rounds/grant_cspace_cap-vc-proving-r1/groups/group_03__callee-error-returns/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Proof reuse hints: none (there was no immediately preceding sealed vc-proving source eligible for comparison)

The group directory must finish with only the copied manual.

## Planned helpers

- prohibited because this case has no active case lib

No helper may be planned or created because this case has no active case lib.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-debug --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-vc-proving-r1 --group callee-error-returns
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-vc-proving-r1 --target-kind group-development --group callee-error-returns
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-vc-proving-r1 --target-kind group-check --group callee-error-returns
```

Debug script: `/home/lixing/projects/QualifiedCProgramming/verification_runs/grant_cspace_cap-20260913165358/_coq_builds/grant_cspace_cap-vc-proving-r1/group_03/src/.coq_debug/group_03_callee_error_returns.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the formal manual and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If the assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `location` must name every affected assigned witness. The controller will seal this group, continue dispatching independent groups, and aggregate all such gaps only after the accepted plan reaches terminal group states.
