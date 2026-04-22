# Issues: array_remove_value_to_output

No blocking issues.

Notes:

- A task-specific Coq definition is needed to express the filtered output prefix.
- The unused suffix of `out` is intentionally existential because the function writes only the kept prefix.
- The contract assumes separated ownership of `a` and `out` through `IntArray::full(a, n, la) * IntArray::full(out, n, lo)`.
