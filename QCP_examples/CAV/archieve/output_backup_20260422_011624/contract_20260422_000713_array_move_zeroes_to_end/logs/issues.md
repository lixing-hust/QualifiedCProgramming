# Contract Issues

## Resolved

- The target behavior needs a topic-specific sequence transformation: stable nonzero filtering followed by zero padding. I kept this out of the C contract body by using `move_zeroes_to_end_spec` in `input/array_move_zeroes_to_end.v`.
- The existing C output lacked the standard verification include headers used by neighboring array contracts. I added `verification_stdlib.h`, `verification_list.h`, and `int_array_def.h`.
- The postcondition now explicitly states `Zlength(move_zeroes_to_end_spec(l)) == n` before the final `IntArray::full`, matching the source length preservation requirement.

## Open

- No unresolved Contract-stage issue.
- Verify-stage work will still need loop invariants and list lemmas for the two-pass in-place update, but those are intentionally not included in this Contract output.
