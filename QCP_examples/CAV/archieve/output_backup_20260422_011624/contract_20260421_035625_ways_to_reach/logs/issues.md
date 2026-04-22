## Issues

No blocking contract issues.

### Decisions

- Added `input/ways_to_reach.v` because the target needs a self-contained recurrence symbol, `ways_to_reach_z`.
- Used `0 <= n && n <= 45` in the precondition to preserve signed 32-bit `int` safety for the returned value and the loop addition `c = a + b`.
- Kept the original function interface and implementation semantics unchanged.

### Validation notes

- `input/ways_to_reach.c` and `input/ways_to_reach.v` contain no `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion.
- `coqtop -quiet < input/ways_to_reach.v` completed successfully.
