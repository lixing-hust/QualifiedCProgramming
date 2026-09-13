# Annotation blocker summary and repair handoff

This is annotation iteration 2 in the run's single persistent annotation-agent session. The controller generated the factual sections and template; the main agent must read the original evidence and replace every `MAIN_AGENT` comment with a concrete summary before running `annotation-summary-ready`. Do not change controller-owned paths, evidence references, or commands.

## Assignment

- Session: `grant_cspace_cap-annotation-agent`
- Round: `grant_cspace_cap-annotation-r2`
- Attempt: `grant_cspace_cap-annotation-r2-attempt-1`
- Retry reason: `annotation-blocked`
- Main root: `/home/lixing/projects/QualifiedCProgramming`
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt2/agent_report.json`
- Human notes: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt2/agent_output.md`

## Target files

- C: `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- `formal_case_lib` candidate (missing in the run topology; there is no active/editable case lib, and this candidate path is read-only and must not be created): `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_manual.v`
- Goal/auto/check: `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal.v`, `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_auto.v`, `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal_check.v`

## Original blocker evidence

- `annotation` / `grant_cspace_cap-annotation-r1-attempt-1`: `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt1/agent_report.json`; `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt1/agent_output.md`

Previous annotation attempt artifacts:

- `grant_cspace_cap-annotation-r1-attempt-1`: report `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt1/agent_report.json`; notes `/home/lixing/projects/QualifiedCProgramming/reports/grant_cspace_cap-20260913165358/annotation-attempts/annotation-attempt1/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "annotation-input", "kind": "missing-target-function", "location": "QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c", "message": "The assigned target function grant_cspace_cap is absent from the current C file. Canonical symbolic execution reports passed but generates only ucos_Grant_Cap obligations, so there is no wrapper implementation or annotation for this owner to verify.", "repair_boundary": "The main agent must add the intended faithful sequential C translation of grant_cspace_cap, including any executable global/type declarations and ENTER_CRITICAL/EXIT_CRITICAL no-op boundaries. Adding executable C is outside the annotation owner's write boundary; after that source repair, continue with this same persistent annotation agent."}

## Main-agent blocker conclusion

The first attempt did not reach a proof obligation for the assigned function: `grant_cspace_cap` was absent from the target C file, so every generated witness belonged to `ucos_Grant_Cap`. This was an annotation-input/source prerequisite failure, not an unprovable VC or a symbolic-execution infrastructure failure. The main root now contains a faithful sequential wrapper body and its required executable globals/types, so a new annotation iteration is required to attach a compositional caller specification and generate the actual `grant_cspace_cap_*` witnesses.

## Evidence and causal analysis

The attempt-1 JSON reports `failure_class: annotation-input`, `kind: missing-target-function`, at `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`. Its Markdown records that canonical symexec passed but `grant_cspace_cap_goal.v` contained only `ucos_Grant_Cap_*` obligations. Thus the passed command was only a symptom of successfully processing the existing callee; it supplied no evidence about the requested wrapper. The root cause was the missing executable wrapper, which also meant there was no caller `Require`/`Ensure`, no footprint for `OSTCBCur`, `OSPrioCur`, `OSRunning`, `OSCSpacePrioTbl`, `CapParent`, or the current CSpace grant-right slot, and no call instantiation connecting those framed resources to the existing `ucos_Grant_Cap` contract. The repaired source now performs the original validation, current-task CSpace lookup, authorization test, callee call, and return-code mapping under sequential no-op critical boundaries.

## Reflection on the previous annotation attempt

The run was initialized under the mistaken assumption that the earlier C case already contained both the verified callee and the wrapper. The useful part to preserve is the existing `ucos_Grant_Cap` implementation/contract and the attempt-1 conclusion that it can serve as the callee interface once the caller owns and frames the surrounding kernel state. Do not repeat the acceptance mistake of treating `status: passed` from symexec as sufficient when the generated goal lacks every `grant_cspace_cap_*` witness. Also do not weaken the wrapper to a contract that discards the shared globals merely to make the call VC local.

## Required annotation repair

Annotate the current `grant_cspace_cap` body with a caller contract that covers all original sequential branches and is strong enough to instantiate `ucos_Grant_Cap`. Its pre-state must provide the current TCB/prio state, writable `OSPrioCur`, `OSRunning`, the current-priority `OSCSpacePrioTbl` entry and non-null current CSpace when needed, the CNode grant-right slot, the relevant `CapParent[dest]` entry, and the destination CSpace/capability resources required by the callee. Its post-state must preserve the framed current-task/authorization resources, reflect the callee's destination capability update exactly on success, preserve destination capability state on failure, and distinguish return values `OS_PRIO_INVALID`, `CNODE_GRANT_FAILURE`, `CSPACE_NONE_FAULT`, and `USER_CAPABILITY_NONE` according to the source branches. Add ordinary assertions/call instantiation where symbolic execution needs the shared footprint split. Modify or strengthen the existing `ucos_Grant_Cap` contract only if composition requires it, and keep its implementation verifiable under the revised contract. This run has no editable `formal_case_lib`; do not create one. Success requires canonical symexec to exit 0 with `status: passed`, generate at least one actual `grant_cspace_cap_*` target witness in addition to any callee witnesses, and pass the complete annotation-checking review without hand-editing generated files or making any concurrency claim.

## Controller scope requirement

Choose local repair or broader redesign from the evidence, and justify the boundary.

## Scope decision

Use a local repair: annotate the newly supplied wrapper and adjust only the directly coupled `ucos_Grant_Cap` contract/assertions when required for the call. The evidence identifies one missing source entry and its immediate caller/callee footprint, not a defect requiring a broad redesign of all OS invariants. Keep `ENTER_CRITICAL/EXIT_CRITICAL` as the documented sequential abstraction for this run; do not introduce CriticalSTS, interrupt-state resources, or unrelated kernel functions.

## Rules to reload

The annotation agent must completely reload both annotation skills on every appended iteration, then follow all linked rules and inspect the original blocker evidence above. The main-agent summary prioritizes the repair but does not replace the original evidence or current main-root files.

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-filling/SKILL.md`
- `.agents/skills/annotation-filling/workflows/annotation-filling.md`
- `.agents/skills/annotation-checking/SKILL.md`
- `.agents/skills/annotation-checking/workflows/annotation-checking.md`

## Writable formal paths

- `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal.v`
- `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_auto.v`
- `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_manual.v`
- `Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Controller command execution contract

Run every listed controller command unchanged with its bound cwd. Prefer a direct system-terminal call. If the runtime
exposes terminal tools only through `functions.exec`, use a transparent bridge. Each bridge cell may await exactly one
terminal operation: `tools.exec_command` to launch the command, or `tools.write_stdin` to continue the same live
session (or the runtime-documented normalized name for that same terminal operation), and may only forward its result.
Pass the rendered command/argv, every argument, and cwd unchanged when launching, and preserve the exact session
handle when continuing. A normalized equivalent is permitted only when its input shape accepts those values unchanged;
never serialize an argv array into shell text, reparse a rendered command, or add quoting.

Do not call a second tool in a bridge cell, add JavaScript/Python orchestration, construct, alter, sequence,
parallelize, or interpret commands, wrap them in a generated shell/PowerShell/Python script or another `uv run`, use
`sh -c`, command substitution, a pipeline or background execution, or invoke another wrapper. Never recreate
controller behavior with a custom command or script.

Preserve every outer cell and inner process/session handle until the actual command reaches a terminal exit. If a
transparent bridge yields a running `functions.exec` cell, resume only that cell with `functions.wait` until its one
nested terminal operation returns. Empty output, an initial-yield response, and outer-cell messages such as
`Script completed` do not prove that the controller command finished. Record a check as passed only after the terminal
process exits with code 0 and the controller JSON reports
`status: passed`.

## Commands

```text
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming symexec --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-annotation-r2
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-annotation-r2 --stage annotation-checking --event start
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run grant_cspace_cap-20260913165358 --round grant_cspace_cap-annotation-r2 --stage annotation-checking --event finish
```

No formal-case-lib Coq command is listed because the optional candidate lib is absent from this run's fixed topology. The controller does not create a placeholder, and the annotation owner must not create a new lib at the read-only candidate path.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

The timing-stage commands are optional telemetry. If used, bracket the real annotation-checking work honestly; they
never replace a check or affect acceptance.

## Completion

Revise the mathematical spec first, editing the case lib only when it is listed as present and writable, then revise C annotations. Never create a missing candidate lib. Use the listed commands when useful for feedback and complete
the semantic annotation review. At the end, success contains only `status: completed`; a blocked result adds one
`blocker` with `failure_class`, `kind`, `location`, `message`, and
`repair_boundary`. Do not copy diff, version, or check results into the report. Notes are optional.
