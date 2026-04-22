# Contract issues: power_nonnegative

## Resolved decisions

- The original function signature is verification-friendly and was preserved.
- The raw domain requirement `exp >= 0` was kept as `0 <= exp`.
- A signed-`int` overflow precondition was added for every prefix power:

```c
forall k, 0 <= k <= exp ->
  INT_MIN <= power_nonnegative_z(base, k) <= INT_MAX
```

- A task-specific Coq file is required because no existing reusable power definition was found in the local CAV inputs or examples, and an unqualified imported name is clearer for the C contract.
- The implementation was kept as the original simple repeated multiplication loop.

## Open issues

- None.

## Notes for Verify

- The contract intentionally contains no loop invariant, assertion, bridge assertion, `which implies`, or loop-exit assertion.
- Verify should connect the loop counter and accumulator to `power_nonnegative_z`; this is deliberately left to the Verify phase.
- The Coq bridge `input/power_nonnegative.v` was checked with `coqc` and parsed successfully.
