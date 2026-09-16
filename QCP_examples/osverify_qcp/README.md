# Shared sequential capability module

The verified C transcriptions keep one function implementation per case. Shared
types, constants and contracts are included; implementations are never included
from another C file.

```text
include/ios_cap_types.h          CSpace/slot/union layout, constants, extern globals
include/ucos_Grant_Cap_spec.h     single Grant declaration and named QCP contracts
ios_cap_globals.c               sole link-time global definitions
cases/ucos_Grant_Cap.c           Grant leaf implementation
cases/ucos_CNode_Delete.c        Delete leaf implementation and contracts
cases/grant_cspace_cap.c         sequential wrapper, calls the shared Grant contract
tests/cap_module_test.c          native linking and behavior smoke test
```

`Rocq/examples/osverify_qcp/cap_model.v` is the shared mathematical dependency.
Its `cap_slot_state` has five storage fields: slot tag, capability tag, two union
words and one pointer. `grant_slot_result` preserves the slot tag and pointer;
`delete_slot_result` preserves the category pointer or the object second word,
as appropriate. The per-case libraries export the same model, rather than copy
its definitions. Grant's contract exposes its three-cell footprint and asserts
the shared transition for arbitrary framed slot-tag/pointer values. Delete
exposes the complete five-field slot transition.

`grant_slot_result` describes the successful valid-target update; invalid class,
priority and null-target behavior remains in the separate named C contracts.
The slot model alone does not encode the whole priority table or CSpace list.

Each function case is verified by its own controller run and formal stem.
The wrapper includes the exact same Grant contract as the leaf: it uses that
contract at the call without importing the Grant implementation. Its result
depends on the separately established leaf contract. Native builds link all
three implementations with `ios_cap_globals.c`; headers never allocate globals.

This is a sequential, framed storage model, not a proof of concurrent critical
sections or a refinement to the legacy whole-OS `OSInv`/CSpace predicates.
Changing a shared contract/model requires reverifying affected implementations
and callers. Historical controller records describe their original source
snapshots, not subsequent refactors. Do not run mutating verification runs
concurrently against this workspace.

Proof trust boundary: the current symbolic executor emits `Admitted` bodies in
`*_proof_auto.v`, including in the pre-refactor tracked Grant artifacts. The
controller checks manual obligations and compiles the assembled goal-check, but
does not turn those auto stubs into kernel-checked Coq proofs. Consequently a
`done` result below is acceptance by the current QCP workflow, not an entirely
admission-free Coq development. The shared mathematical model has no admissions;
manual proof completion is checked separately by the controller. Eliminating
the generated-auto trust boundary is a separate framework/proof-export task.

The native smoke test is supplementary; it does not replace VC proofs or the
controller final check.

## Refactor verification results (2026-09-16)

Each row has its own source file, generated family and completed controller run.
The counts exclude auxiliary split goals. Auto counts describe generated
automatic obligations subject to the trust boundary above, not proved Coq bodies.

| Function | Auto obligations | Proved manual VCs | Controller result |
|---|---:|---:|---|
| `ucos_Grant_Cap` | 22 | 1 | [done](../../reports/ucos_Grant_Cap-20260916223647/controller_state.json) |
| `ucos_CNode_Delete` | 37 | 3 | [done](../../reports/ucos_CNode_Delete-20260916225404/controller_state.json) |
| `grant_cspace_cap` | 39 | 9 | [done](../../reports/grant_cspace_cap-20260916230710/controller_state.json) |

All three final checks passed, including freshness, full goal-check compilation,
manual structure and cleanup. Delete and wrapper specifications were frozen for
their runs. The wrapper generated family contains only wrapper obligations and
uses the shared Grant contract at its call. All three executable function bodies
were mechanically compared with their pre-refactor bodies and are unchanged.
The native linked smoke test passed with AddressSanitizer/UBSan enabled (with the
LeakSanitizer exception below). The shared model and case manual files contain
no `Admitted` or additional `Axiom` declarations.

## Native smoke test

For a native test, run from the repository root (the include root is intentional:
the controller rejects quoted include paths containing `..`):

```sh
cap_test_dir=$(mktemp -d /tmp/qcp-cap-module.XXXXXX)
gcc -std=c11 -Wall -Wextra -fsanitize=address,undefined -g \
  -IQCP_examples/osverify_qcp \
  QCP_examples/osverify_qcp/tests/cap_module_test.c \
  QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c \
  QCP_examples/osverify_qcp/cases/ucos_CNode_Delete.c \
  QCP_examples/osverify_qcp/cases/grant_cspace_cap.c \
  QCP_examples/osverify_qcp/ios_cap_globals.c \
  -o "$cap_test_dir/cap_module_test"
ASAN_OPTIONS=detect_leaks=0 "$cap_test_dir/cap_module_test"
```

Leak detection is disabled because the managed execution environment does not
support LeakSanitizer under ptrace; address and undefined-behavior checks remain
enabled. The inherited unsigned comparison with zero in Grant may produce a
compiler warning; it is retained to preserve the legacy executable body.
