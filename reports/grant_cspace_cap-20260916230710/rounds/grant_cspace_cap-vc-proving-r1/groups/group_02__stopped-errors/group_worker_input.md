# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `stopped-errors`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Helpers: prohibited because this case has no active case lib


### `proof_of_grant_cspace_cap_return_wit_7_callee_null` — `LLM_pre_process`

Strategy: Keep the OSRunning UChar cell while extracting its value range 0 <= running <= 255. This bounds running below 2^32, so unsigned_last_nbits running 32 = running; PreH3 gives running = 0. Choose the second RHS disjunct, rewrite target = 0, and reorder/cancel the destination-table cell and seven global/frame cells.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_grant_cspace_cap_return_wit_8_callee_invalid` — `LLM_pre_process`

Strategy: Extract running's unsigned-byte range from its owned OSRunning cell without consuming it. Reduce its 32-bit truncation to running, obtaining running = 0 from PreH3. Choose the fourth RHS disjunct, use PreH23 for class > 16, and cancel all seven unchanged cells; no target = 0 premise is needed.

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

- Copied manual: `/home/lixing/projects/QualifiedCProgramming/verification_runs/grant_cspace_cap-20260916230710/grant_cspace_cap-vc-proving-r1/groups/group_02__stopped-errors/grant_cspace_cap_proof_manual.v`
- Active case lib: none; no `group_worker_lib` exists for this group
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260916230710/rounds/grant_cspace_cap-vc-proving-r1/groups/group_02__stopped-errors/group_worker_report.json`
- Notes: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260916230710/rounds/grant_cspace_cap-vc-proving-r1/groups/group_02__stopped-errors/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-debug --run grant_cspace_cap-20260916230710 --round grant_cspace_cap-vc-proving-r1 --group stopped-errors
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run grant_cspace_cap-20260916230710 --round grant_cspace_cap-vc-proving-r1 --target-kind group-development --group stopped-errors
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming coq-check --run grant_cspace_cap-20260916230710 --round grant_cspace_cap-vc-proving-r1 --target-kind group-check --group stopped-errors
```

Debug script: `/home/lixing/projects/QualifiedCProgramming/verification_runs/grant_cspace_cap-20260916230710/_coq_builds/grant_cspace_cap-vc-proving-r1/group_02/src/.coq_debug/group_02_stopped_errors.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the formal manual and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If the assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `location` must name every affected assigned witness. The controller will seal this group, continue dispatching independent groups, and aggregate all such gaps only after the accepted plan reaches terminal group states.
