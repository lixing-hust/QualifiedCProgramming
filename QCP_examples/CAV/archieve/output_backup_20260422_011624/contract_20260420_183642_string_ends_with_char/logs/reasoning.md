# Contract reasoning: string_ends_with_char

## Source semantics

The raw task defines `string_ends_with_char(char *s, char c)`.

The input `s` is a valid C-style string terminated by `0`. The function scans to the final character before the terminator. It returns `1` exactly when the string is nonempty and that final character equals `c`; otherwise it returns `0`. The function does not modify the string and returns only `0` or `1`.

## Interface decision

The original interface is already suitable for verification:

- `s` is caller-provided readable character memory.
- `c` is a scalar character value.
- The function returns an `int` boolean.
- No allocation, I/O, global state, or test scaffolding is involved.

The implementation is rewritten only in surface form to use `while (1)` plus explicit `0` checks, following the local verification-friendly string scanning pattern. This preserves the source semantics.

## Memory model

Use `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, where:

- `l` is the logical list of non-terminator string characters.
- `n` is the logical string length.
- the final array cell is the C string terminator `0`.

Because the implementation stops at the first `0`, the precondition must rule out internal terminators:

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

This makes the loop exit position coincide with the final terminator of the represented string.

The function is read-only, so the postcondition restores the same `CharArray::full` predicate.

## Bounds and overflow

Require `0 <= n && n < INT_MAX`. The implementation uses `int i` and reads `s[i + 1]` after confirming the string is nonempty. With `n < INT_MAX`, indices up to `n` and expressions `i + 1` remain within `int` bounds during the scan.

## Functional postcondition

The result is specified directly:

- if `n == 0`, return `0`;
- if `0 < n` and `l[n - 1] == c`, return `1`;
- if `0 < n` and `l[n - 1] != c`, return `0`.

This directly captures the task statement and uses only existing list indexing syntax already used in nearby contracts. No additional Coq helper definition is needed.

## Coq dependency decision

No `input/string_ends_with_char.v` is required. The specification does not need a recursive list function or task-specific bridge predicate; it can be expressed completely in the C contract using `CharArray::full`, `app`, `cons`, quantification, and list indexing.
