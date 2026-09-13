# Annotation blocker summary and repair handoff

This is annotation iteration 2 in the run's single persistent annotation-agent session. The controller generated the factual sections and template; the main agent must read the original evidence and replace every `MAIN_AGENT` comment with a concrete summary before running `annotation-summary-ready`. Do not change controller-owned paths, evidence references, or commands.

## Assignment

- Session: `ucos_Grant_Cap-annotation-agent`
- Round: `ucos_Grant_Cap-annotation-r2`
- Attempt: `ucos_Grant_Cap-annotation-r2-attempt-1`
- Retry reason: `annotation-blocked`
- Main root: `/home/lixing/projects/QualifiedCProgramming`
- Terminal report: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt2/agent_report.json`
- Human notes: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt2/agent_output.md`

## Target files

- C: `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- `formal_case_lib` candidate (missing in the run topology; there is no active/editable case lib, and this candidate path is read-only and must not be created): `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_manual.v`
- Goal/auto/check: `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal.v`, `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_auto.v`, `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal_check.v`

## Original blocker evidence

- `annotation` / `ucos_Grant_Cap-annotation-r1-attempt-1`: `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt1/agent_report.json`; `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt1/agent_output.md`

Previous annotation attempt artifacts:

- `ucos_Grant_Cap-annotation-r1-attempt-1`: report `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt1/agent_report.json`; notes `/home/lixing/projects/QualifiedCProgramming/reports/ucos_Grant_Cap-20260910000144/annotation-attempts/annotation-attempt1/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "annotation-input", "kind": "unsupported-c-declaration-form", "location": "QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c:55", "message": "Canonical symbolic execution cannot parse the forward typedef `typedef struct cspace CSPACE;` because the QCP C frontend requires `struct cspace` to be declared or defined before that use. This fails before any annotation can be checked.", "repair_boundary": "The main agent must make the semantics-preserving source-level type-declaration rewrite `typedef struct cspace { ... } CSPACE;` (or another parser-supported equivalent). The annotation owner may then continue in this same persistent session and construct the function contract."}

## Main-agent blocker conclusion

The first annotation attempt was blocked before any VC or annotation check was produced: canonical symbolic execution rejected the forward typedef at `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c:55`. This is an annotation-input/source-compatibility defect, not a mathematical-specification or Rocq-proof failure. A second iteration is required so the same annotation owner can work from a parser-accepted but semantically equivalent C declaration.

## Evidence and causal analysis

The attempt-1 report records `failure_class: annotation-input`, `kind: unsupported-c-declaration-form`, and the first diagnostic `Use of undeclared type struct cspace` at line 55. Its notes confirm that the failure occurred before annotation processing and that the generated-file transaction rolled back, so there are no witnesses, contracts, invariants, assertions, or call instantiations to repair yet. The root cause is the two-stage declaration `typedef struct cspace CSPACE;` followed by `struct cspace { ... };`, which this frontend does not support; the function body and intended capability update were not reached.

## Reflection on the previous annotation attempt

The intake scaffold assumed the frontend accepted ordinary C forward-tag typedefs. That assumption was too broad for QCP's parser. Preserve the exact constants, field order, nested struct/union layout, global 64-entry table, branch order, and rights-update expression from the scaffold. Do not reintroduce a separate forward typedef, and do not compensate by flattening the CSpace layout or changing the verified algorithm.

## Required annotation repair

The main-root C declaration has been locally rewritten to a combined `typedef struct cspace { ... } CSPACE;`, using `struct cspace *` for the two self-referential fields. Reload the current C file, construct a strong function contract in that file, and add only the assertions needed to establish exact failure preservation and the one-slot success update. The run topology has no editable `formal_case_lib`; do not create `ucos_Grant_Cap_lib.v`. Success requires the listed canonical symexec command to report `status: passed`, generated artifacts to arise only from that command, and annotation-checking to confirm unsigned bounds, null/failure framing, exact `(old_right & 4095) | cap_Right` semantics, and preservation of every unrelated resource without `Admitted`, `Abort`, or extra axioms.

## Controller scope requirement

Choose local repair or broader redesign from the evidence, and justify the boundary.

## Scope decision

Use a local repair. The diagnostic identifies one unsupported declaration form and gives no evidence that the capability contract or overall representation design is wrong. The combined declaration is layout- and behavior-preserving, so a broader source redesign would add risk without addressing any observed blocker.

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
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_auto.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_manual.v`
- `Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal_check.v`

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
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming symexec --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r2
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r2 --stage annotation-checking --event start
/home/lixing/.local/share/uv/python/cpython-3.12.13-linux-x86_64-gnu/bin/python3.12 /home/lixing/projects/QualifiedCProgramming/.agents/scripts/verification-orchestrator/controller.py --main-root /home/lixing/projects/QualifiedCProgramming timing-stage --run ucos_Grant_Cap-20260910000144 --round ucos_Grant_Cap-annotation-r2 --stage annotation-checking --event finish
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
