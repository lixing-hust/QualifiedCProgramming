# Contract issues: fibonacci

## Resolved decisions

- The original function signature is verification-friendly and was preserved.
- A signed `int` overflow boundary was added: `0 <= n && n <= 46`.
- A task-specific Coq file is required because no existing reusable Fibonacci definition was found in the local CAV inputs.

## Open issues

- None.

## Notes for Verify

- The contract intentionally contains no loop invariant, assertion, bridge assertion, `which implies`, or loop-exit assertion.
- Verify should connect the rolling variables to `fib_z`; this is deliberately left to the Verify phase.
