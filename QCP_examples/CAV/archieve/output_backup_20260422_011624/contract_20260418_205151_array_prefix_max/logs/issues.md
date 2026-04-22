## Status

No blocking contract issues.

## Notes

- The contract uses disjoint ownership for `a` and `out` via separating conjunction. If a later task needs overlap or exact aliasing behavior, that should be treated as an interface change and handled explicitly at the contract stage.
- `input/array_prefix_max.v` is intentionally omitted because the existing `max_list_nonempty` definition is sufficient.
