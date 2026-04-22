# Issues: climbStairs

## Issue 1: Missing reusable Coq symbol for climb-stairs semantics
- Observation: No existing shared `Extern Coq` symbol for this exact LeetCode semantics was found in this workspace.
- Risk: If C spec used an undefined logical symbol, Verify input would not typecheck.
- Decision: Added minimal task-local bridge file `input/climb_stairs.v` and imported it from C.

## Issue 2: Potential integer overflow in iterative recurrence
- Observation: recurrence grows as Fibonacci; unrestricted `n` causes int overflow.
- Risk: Undefined behavior in C addition and mismatch with mathematical spec.
- Decision: constrained precondition to `0 <= n <= 45` to keep all intermediate sums and final return in signed 32-bit range.

## Issue 3: Annotate/Verify boundary separation
- Observation: DP loops often tempt adding loop invariants early.
- Risk: Violates annotate-stage responsibility and pollutes contract-only output.
- Decision: Kept only complete `Require/Ensure`; did not add `Inv`, `Assert`, bridge-assert, `which implies`, or exit assertions.
