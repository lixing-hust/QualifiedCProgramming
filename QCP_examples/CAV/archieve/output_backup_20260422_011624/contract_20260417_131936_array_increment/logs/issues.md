## Status

No blocking issues in contract generation.

## Notes

- The raw statement already provides the exact overflow-side assumption needed for `a[i] + 1`.
- The optional `input/array_increment.v` was intentionally not created because the contract can be expressed with existing list primitives and `IntArray::full`.
