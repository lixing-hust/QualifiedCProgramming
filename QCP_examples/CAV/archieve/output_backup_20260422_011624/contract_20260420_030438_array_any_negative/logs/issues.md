## Status

No blocking issues in contract generation.

## Notes

- The raw statement is complete and the original interface is verification-friendly.
- The array is read-only, so the postcondition preserves `IntArray::full(a, n, l)`.
- The optional `input/array_any_negative.v` was intentionally not created because the specification can be written directly with quantified conditions over `l`.
