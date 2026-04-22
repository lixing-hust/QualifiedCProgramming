## Issues

- No blocking issues in the raw statement.
- The generated contract treats `src` and `dst` as separately owned arrays. If overlapping buffers must be supported later, that would require a different contract shape and likely a more alias-aware verification strategy.
- `input/copy_array.v` was not created because the function semantics are fully expressible with existing list and array predicates.
