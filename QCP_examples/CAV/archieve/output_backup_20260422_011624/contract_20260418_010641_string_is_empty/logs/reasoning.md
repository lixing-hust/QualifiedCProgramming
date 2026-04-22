## Function

`string_is_empty`

## Semantic Summary

The function reads the first byte of a null-terminated string `s`.

- If `s[0] == '\0'`, it returns `1`.
- Otherwise it returns `0`.
- The function does not modify memory.

This is equivalent to checking whether the logical string length is zero.

## Memory Model Choice

Use the repository's standard null-terminated string shape:

`CharArray::full(s, n + 1, app(l, cons(0, nil)))`

where:

- `n` is the logical length of the string
- `l` is the list of non-terminator characters before the final `0`

This matches existing local conventions such as `input/string_length.c`.

## Preconditions

Use:

- `0 <= n`
- `n < INT_MAX`
- `CharArray::full(s, n + 1, app(l, cons(0, nil)))`

Rationale:

- `n + 1` must be a valid array size expression for the model.
- The null-terminated shape guarantees that `s[0]` is readable.
- No stronger value constraint is needed because the implementation only inspects the first character.

## Postcondition Shape

The function is pure with respect to memory, so preserve the same `CharArray::full(...)`.

The return value is characterized directly by `n`:

- `n == 0` implies `__return == 1`
- `0 < n` implies `__return == 0`

This avoids introducing a custom Coq definition because the semantics are simple and already expressible in C-level logic.

## Coq Dependency Decision

No `input/string_is_empty.v` is needed.

Reason:

- The spec can be written directly with existing integer logic and `CharArray::full`.
- There is no need for a problem-specific bridge predicate or auxiliary mathematical function.
