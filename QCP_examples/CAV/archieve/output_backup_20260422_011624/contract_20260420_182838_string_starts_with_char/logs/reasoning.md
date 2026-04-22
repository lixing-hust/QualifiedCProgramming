# Contract Reasoning: string_starts_with_char

## Source Semantics

The raw implementation reads only the first byte of a valid C-style string `s`.

- If `s[0] == 0`, the string is empty and the function returns `0`.
- Otherwise, if `s[0] == c`, the function returns `1`.
- Otherwise, it returns `0`.

The function does not write through `s`, allocate memory, or access any index other than `0`.

## Contract Shape

Use the standard CAV string representation:

- `l` is the logical content before the terminator.
- `n` is the logical string length.
- `CharArray::full(s, n + 1, app(l, cons(0, nil)))` owns the full string buffer including the terminator.
- `forall k, 0 <= k < n => l[k] != 0` records that the logical string content has no earlier terminator.

Although the implementation only checks `s[0]`, this is still a C-style string contract, so the normal no-internal-terminator premise is included to make `n == 0` exactly characterize the empty string.

## Result Semantics

The output is fully described by cases:

- `n == 0`: return `0`, including when `c == 0`.
- `0 < n && l[0] == c`: return `1`.
- `0 < n && l[0] != c`: return `0`.

The postcondition restores the unchanged `CharArray::full` predicate for `s`.

## Coq Dependency Decision

No task-specific Coq definition is needed. The result relation is small enough to write directly as a disjunction in `Ensure`, so `input/string_starts_with_char.v` is not created.
