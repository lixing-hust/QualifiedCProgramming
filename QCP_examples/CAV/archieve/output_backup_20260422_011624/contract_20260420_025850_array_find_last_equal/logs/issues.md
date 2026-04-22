# Issues: array_find_last_equal

No blocking issues.

Notes:

- The raw interface is already verification-friendly: a scalar length, an input integer array, and a scalar key.
- The function is read-only with respect to the array, so no interface rewrite is needed.
- `input/array_find_last_equal.v` is not needed because the result relation is simple enough to state directly in the C contract.
