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
cases/ucos_CNode_Mint.c          rights-restricting Mint implementation and contracts
cases/ucos_CNode_Mutate.c        Mutate implementation, updates source and destination
cases/grant_cspace_cap.c         sequential wrapper, calls the shared Grant contract
tests/cap_module_test.c          native linking and behavior smoke test
tests/cap_mint_test.c            Mint success, failure and aliasing regression tests
tests/cap_mutate_test.c          Mutate mask, frame and aliasing regression tests
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

## Mint example

`ucos_CNode_Mint` is transcribed from the function in
`../osverify/certiucos/code/ios_cap.v`. Its case library exports the existing
shared slot model and defines `mint_authorized`, `minted_slot` and
`mint_slot_transition`. Success requires a category capability and requested
rights that are a strict bitwise subset of the source rights. It copies the
source content and requested rights into the destination, preserving the
destination slot tag and pointer. Failure returns 5 without changing storage.

The contracts distinguish one priority-table entry, two entries pointing to the
same CSpace, and two distinct CSpaces. Both aliasing cases own only one capability
footprint. In particular, an aliased successful call changes the source rights
too; source preservation is claimed only for distinct CSpaces. Invalid class,
priority and null entries are covered by separate contracts.

This retains the legacy function's decision and update behavior, but does not
import or prove equivalence to its whole-OS legacy specification. No critical
section or concurrent interference is modeled. The shared C header and shared
Coq model are unchanged by this example.

Verification completed on 2026-09-17 using the verification-orchestrator and
final-check workflow. Run
[`ucos_CNode_Mint-20260917000112`](../../reports/ucos_CNode_Mint-20260917000112/controller_state.json)
is `done`: all 12 manual return VCs and their 12 split goals were proved, four
groups were accepted, and parent/full goal-check, independent freshness,
structure and cleanup checks passed. No group helper was needed; the manual
and case library contain no admissions. Native regression with ASan/UBSan also
passed (leak detection disabled as described below).

The generated auto file contains **80 `Admitted` proof bodies** (48 safety,
8 early returns and 24 partial-solve obligations). This is the current
generator's proof-export limitation described above, so the run is not an
admission-free end-to-end Coq proof. Its 12 completed manual VCs must not be
reported as 92 kernel-proved obligations.

## Mutate example

`ucos_CNode_Mutate` follows `ucos_CNode_Mutate_impl` in legacy `ios_cap.v`.
For distinct CSpaces, successful mutation copies source content and requested
rights into the destination, removes those rights from the source, and sets the
source slot tag to `SLOT_NULL_CAP`. The source capability type is **not** cleared.
Both pointers, source content/type, and destination slot tag are preserved.
The requested rights must be a strict subset of source rights; invalid indices,
null entries and rejected capabilities return 8 without changing storage.

The original `ucos_CNode_MutatePre'` in `CapSpec.v` assumes destination priority
greater than source priority and uses whole-OS predicates. The sequential
storage model here additionally describes actual same-priority and shared-pointer
behavior: an aliased successful call leaves one slot with tag 0, capability
type 1, original content, **rights 0**, and unchanged pointer. This follows the
write-then-read-modify-write order, not an invented distinct-space assumption.
These extra cases are not a claim of equivalence to the original whole-OS spec.
The existing shared header/model and prior examples are unchanged.

Run
[`ucos_CNode_Mutate-20260917145310`](../../reports/ucos_CNode_Mutate-20260917145310/controller_state.json)
completed on 2026-09-17 with `phase: done`. The verification-orchestrator and
final-check workflow accepted all four groups: 12 manual return VCs and their
12 split goals are proved, with no new helper. Parent/full goal-check,
independent freshness, structure and cleanup checks passed on the first
annotation/proving rounds. The native regression passed with ASan/UBSan (leak
detection disabled). The case library and manual have no `Admitted`, `Abort`,
`Axiom` declarations or `Show` commands.

The generated auto file still contains **83 `Admitted` proof bodies**. As with
Mint, `done` means acceptance by the current workflow, not an admission-free
end-to-end Coq proof. The original whole-OS and concurrency proof boundary
remains unchanged.

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

The separate Mint regression covers rejected inputs, permission subsets,
unchanged failure state, both aliasing layouts and the high unsigned rights bit:

```sh
mint_test_dir=$(mktemp -d /tmp/qcp-cap-mint.XXXXXX)
gcc -std=c11 -Wall -Wextra -fsanitize=address,undefined -g \
  -IQCP_examples/osverify_qcp \
  QCP_examples/osverify_qcp/tests/cap_mint_test.c \
  QCP_examples/osverify_qcp/cases/ucos_CNode_Mint.c \
  QCP_examples/osverify_qcp/ios_cap_globals.c \
  -o "$mint_test_dir/cap_mint_test"
ASAN_OPTIONS=detect_leaks=0 "$mint_test_dir/cap_mint_test"
```

The Mutate regression exhausts all pairs of five-bit rights masks in each of
three pointer layouts (3,072 cases), checks high-bit rights and boundary classes,
and compares complete CSpace/table storage against expected updates:

```sh
mutate_test_dir=$(mktemp -d /tmp/qcp-cap-mutate.XXXXXX)
gcc -std=c11 -Wall -Wextra -fsanitize=address,undefined -g \
  -IQCP_examples/osverify_qcp \
  QCP_examples/osverify_qcp/tests/cap_mutate_test.c \
  QCP_examples/osverify_qcp/cases/ucos_CNode_Mutate.c \
  QCP_examples/osverify_qcp/ios_cap_globals.c \
  -o "$mutate_test_dir/cap_mutate_test"
ASAN_OPTIONS=detect_leaks=0 "$mutate_test_dir/cap_mutate_test"
```

Leak detection is disabled because the managed execution environment does not
support LeakSanitizer under ptrace; address and undefined-behavior checks remain
enabled. The inherited unsigned comparison with zero in Grant, Mint and Mutate may produce a
compiler warning; it is retained to preserve the legacy executable body.
