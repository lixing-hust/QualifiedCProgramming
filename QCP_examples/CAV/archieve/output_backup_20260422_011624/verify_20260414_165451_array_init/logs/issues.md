# Verify Issues

## Resolved

### 1. Workspace include paths broke after copying `input/array_init.c`

The original source uses:

- `#include "../../verification_stdlib.h"`
- `#include "../../verification_list.h"`
- `#include "../../int_array_def.h"`

Those paths are correct from `input/`, but not from `output/.../annotated/`. The workspace copy was updated to:

- `#include "../../../../verification_stdlib.h"`
- `#include "../../../../verification_list.h"`
- `#include "../../../../int_array_def.h"`

This change was applied only in `annotated/array_init.c`.

### 2. Extra loop-exit assertion caused `symexec` failure

The first annotated version added a final exit assertion after the loop. `symexec` failed with:

- `Fail to Remove Memory Permission of i`

The failure came from replacing the symbolic state near function exit with a manual assertion that no longer matched local-variable cleanup. The fix was to remove that exit assertion and rely on the natural loop-exit state generated from the invariant.

### 3. Shared strategy `.vo` files were missing

`array_init_goal.v` imports:

- `int_array_strategy_goal/proof`
- `uint_array_strategy_goal/proof`
- `undef_uint_array_strategy_goal/proof`
- `array_shape_strategy_goal/proof`

In this environment, the corresponding `.vo` files were not present in `SeparationLogic/examples/`, and compiling them there was blocked because that directory is outside the writable workspace.

Workaround used:

- copy the required strategy `.v` files into `coq/deps/`
- compile them inside the workspace
- add `coq/deps/` as an extra `-R ... SimpleC.EE` load path when compiling the generated files

This kept all writes inside the allowed workspace and allowed `goal_check.v` to compile successfully.

## Remaining

### Temporary compilation artifacts remain in the workspace

The workspace now contains `.aux`, `.glob`, `.vo`, `.vos`, and `.vok` files under:

- `coq/generated/`
- `coq/deps/`

I attempted to clean them, but shell deletion commands were blocked by the environment policy. This does not affect verification correctness; it only leaves extra build artifacts in the workspace.

## Recheck

### 2026-04-14 command-line compile chain revalidated

I reran the full command-line compile chain from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with:

- workspace-local `-R .../coq/deps SimpleC.EE`
- workspace-local `-R .../coq/generated SimpleC.EE.leetcode.verify_20260414_165451_array_init`

Recheck result:

- `array_init_goal.v`: pass
- `array_init_proof_auto.v`: pass
- `array_init_proof_manual.v`: pass
- `array_init_goal_check.v`: pass
