# Contract Issues: array_has_adjacent_equal

## Decisions

- Kept the original interface `int array_has_adjacent_equal(int n, int *a)` because it is already verification-friendly: a single read-only array input and an integer boolean result.
- Used `IntArray::full(a, n, l)` with `Zlength(l) == n` to capture both memory ownership and array values.
- Specified adjacent equality directly with quantifiers over `1 <= i && i < n`.
- Did not create `input/array_has_adjacent_equal.v` because no task-specific Coq helper or bridge predicate is required.

## Issues

- No contract blockers encountered.
- No source-interface rewrite was required.
- No experience document update was required.
