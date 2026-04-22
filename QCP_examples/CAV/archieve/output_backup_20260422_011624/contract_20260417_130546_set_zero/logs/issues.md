No blocking issues.

Decisions:

- kept the original signature unchanged
- did not create `input/set_zero.v`

Non-issues checked:

- null pointer handling is intentionally not specified separately; ownership is already captured by `IntArray::full(a, n, l)`
- no overflow constraints are needed because the function only stores the constant `0`
- no extra postcondition about preserving old contents is needed because the whole array is overwritten
