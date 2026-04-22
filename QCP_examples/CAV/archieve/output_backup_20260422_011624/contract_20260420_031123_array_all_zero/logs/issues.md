## Status

No blocking issues in contract generation.

## Notes

- The raw statement already gives the required input domain: `n >= 0`, exact array length `n`, and read-only behavior.
- The result semantics were expressed directly with quantifiers in the C contract.
- The optional `input/array_all_zero.v` was intentionally not created because no problem-specific Coq definition is needed.
