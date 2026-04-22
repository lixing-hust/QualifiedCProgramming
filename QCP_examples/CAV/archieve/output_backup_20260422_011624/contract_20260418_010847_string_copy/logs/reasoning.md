## Function

`string_copy(char *src, char *dst)` copies the bytes of the null-terminated string in `src` into `dst`, then writes the final `'\0'`.

## Semantic Choices

- Model `src` as a C string using `CharArray::full(src, n + 1, app(l, cons(0, nil)))`.
- Model `dst` as a separate allocated writable buffer of the same size using `CharArray::full(dst, n + 1, d)`.
- Preserve the implementation exactly: same parameters, same loop, same final terminator write.

## Boundary Conditions

- `n >= 0` allows the empty string case.
- `n < INT_MAX` keeps `n + 1` in range and matches the `int i` loop index.
- The destination must have room for all `n` characters plus the trailing `0`.

## Memory Model

- The contract uses separating conjunction between `src` and `dst`, so the buffers are disjoint.
- This is verification-friendly and avoids aliasing cases where writing `dst[i]` could mutate future reads from `src[i]`.
- `src` is unchanged after the call.
- `dst` contains the exact string copied from `src`, including the trailing `0`.

## Coq Dependency Decision

- No extra `input/string_copy.v` is needed.
- Existing repository predicates for character arrays and null-terminated strings are sufficient.
