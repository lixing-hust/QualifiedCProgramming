# Issues: array_move_zeroes_to_end

## Resolved

- The raw interface was already suitable for verification; no interface rewrite
  was needed.
- The stable-compaction semantics are not pointwise, so a task-specific Coq
  definition was added in `input/array_move_zeroes_to_end.v`.

## Open

- None for the contract stage.

## Verification notes

- No invariants, assertions, bridge assertions, or loop-exit assertions were
  added. Those remain Verify-stage responsibilities.
