# Contract issues: array_count_even

## Resolved

- The natural-language statement says the function does not modify the array. The contract preserves `IntArray::full(a, n, l)` in the postcondition, so the memory/content preservation is explicit.
- The parity predicate is source-level `x % 2 == 0`. The Coq spec uses `Z.rem x 2 = 0` so negative even values are counted consistently with the C test.
- The result semantics are not a built-in public Coq function, so a minimal task-specific `input/array_count_even.v` was added.

## Open issues

- None at the contract stage.

## Verify-stage notes

- The verifier will likely need the standard array-count loop summary that the scalar counter equals the spec over the processed prefix.
- It may also need helper lemmas for appending one element to `array_count_even_spec` and bounding the count by the prefix length, following the existing `array_count_zero` and `count_positive` patterns.
