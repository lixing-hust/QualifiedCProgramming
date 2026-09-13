# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `UserAddrCheck-annotation-r1`
- Attempt: `UserAddrCheck-annotation-r1-attempt-1` (index 1)
- Main root: `/home/lixing/projects/QualifiedCProgramming`
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/UserAddrCheck-20260909232431/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/home/lixing/projects/QualifiedCProgramming/reports/UserAddrCheck-20260909232431/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/osverify_qcp/cases/UserAddrCheck.c`
- `formal_case_lib` candidate (missing in the run topology; there is no active/editable case lib, and this candidate path is read-only and must not be created): `Rocq/examples/osverify_qcp/cases/UserAddrCheck_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/osverify_qcp/cases/UserAddrCheck_proof_manual.v`
- Goal/auto/check: `Rocq/examples/osverify_qcp/cases/UserAddrCheck_goal.v`, `Rocq/examples/osverify_qcp/cases/UserAddrCheck_proof_auto.v`, `Rocq/examples/osverify_qcp/cases/UserAddrCheck_goal_check.v`

## Rules to read

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-filling/SKILL.md`
- `.agents/skills/annotation-filling/workflows/annotation-filling.md`
- `.agents/skills/annotation-checking/SKILL.md`
- `.agents/skills/annotation-checking/workflows/annotation-checking.md`

## Previous attempts

- none

Required lessons:

- none

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


## Persistent annotation agent

- Session: `UserAddrCheck-annotation-agent`
- Iteration: 1

This is the initial iteration. Read both annotation skill files completely, follow their linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

## Problem context

- Problem Statement: Faithfully port and verify the integer UserAddrCheck_impl from QCP_examples/osverify/certiucos/code/ifun_useraddrchk.v using QCP.
- Target Function: UserAddrCheck
- Expected Behavior: For a uint32 address a, return 0 iff a <= 0 or 4294867295 < a; otherwise return 1. Preserve the legacy control flow and constants.
- Input Output Contract: Input is the mathematical unsigned value of addr in [0,4294967295]. No memory is accessed. Return is 0 on the legacy out-of-range condition and 1 on the legacy in-range condition.
- Spec Hint: Legacy implementation: if UserAddrStart >= addr or addr > UserAddrEnd return 0, else return 1; UserAddrStart=0 and UserAddrEnd=4294867295.
- Forbidden Patterns: Do not change the function body, constants, integer types, branch condition, or return values.

## Writable formal paths

- `QCP_examples/osverify_qcp/cases/UserAddrCheck.c`
- `Rocq/examples/osverify_qcp/cases/UserAddrCheck_goal.v`
- `Rocq/examples/osverify_qcp/cases/UserAddrCheck_proof_auto.v`
- `Rocq/examples/osverify_qcp/cases/UserAddrCheck_proof_manual.v`
- `Rocq/examples/osverify_qcp/cases/UserAddrCheck_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Frozen specification

The specification of `UserAddrCheck` is a fixed input for this run, not something to
redesign. Their `With` / `Require` / `Ensure` blocks -- including named specs and any
`<= other_spec` clause -- must survive this attempt token-identical. Comments, whitespace
and line endings are free.

Because a frozen specification's meaning depends on the definitions behind it, every
`Extern Coq` entry, `Import Coq` module, and case-lib declaration that already exists is
frozen as well.

You may still add: new `Extern Coq` entries, new imports, new case-lib definitions and
lemmas, and specifications for functions not listed above. Every `Inv Assert` and `Assert`
stays fully editable -- those are the intended working surface.

Controller acceptance re-extracts this surface and compares it entry by entry. A changed or
removed entry fails the attempt and returns here naming the exact entry, so weakening a
frozen specification to make a proof close is not a route forward.

## Commands

```text
/home/lixing/projects/QualifiedCProgramming/.venv/bin/python3 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming symexec --run UserAddrCheck-20260909232431 --round UserAddrCheck-annotation-r1
/home/lixing/projects/QualifiedCProgramming/.venv/bin/python3 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run UserAddrCheck-20260909232431 --round UserAddrCheck-annotation-r1 --stage annotation-checking --event start
/home/lixing/projects/QualifiedCProgramming/.venv/bin/python3 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run UserAddrCheck-20260909232431 --round UserAddrCheck-annotation-r1 --stage annotation-checking --event finish
```

No formal-case-lib Coq command is listed because the optional candidate lib is absent from this run's fixed topology. The controller does not create a placeholder, and the annotation owner must not create a new lib at the read-only candidate path.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

The timing-stage commands are optional telemetry. If used, bracket the real annotation-checking work honestly; they
never replace a check or affect acceptance.

## Completion

Design the mathematical spec first, editing `formal_case_lib` only when it is listed as present and writable, then revise C annotations and complete annotation-checking. Never create a missing candidate lib.
Use the listed commands when useful for feedback; controller acceptance reruns every mandatory machine check. Write
a success report containing only `status: completed`; a blocked result adds one
complete `blocker`. Do not copy changed paths, version, or check status into the report.
