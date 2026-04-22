## Semantics

Target function: `string_contains_char(char *s, char c)`.

The function scans a valid C string from left to right and returns:

- `1` if some character before the terminator equals `c`
- `0` otherwise

The string is read-only and unchanged by the function.

## Boundary and memory decisions

Use the repository's standard C-string shape:

`CharArray::full(s, n + 1, app(l, cons(0, nil)))`

Because control flow stops at the first `0`, add the standard no-internal-terminator assumption:

`(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`

This ensures the loop scans exactly the logical string contents `l` and the final extra cell is the unique terminator.

The function does not modify memory, so the postcondition preserves the same `CharArray::full(...)`.

`n < INT_MAX` is included so the index variable `i` can range over the whole string length without overflowing an `int`.

## Coq dependency decision

This task needs a small dedicated Coq helper.

Reason:

- The result is naturally a list-search specification over the logical string contents.
- Existing public arithmetic/string definitions in the repository are not enough to express the exact `0/1` return behavior directly in the C contract.
- A tiny `string_contains_char_spec : list Z -> Z -> Z` keeps the C contract short and matches repository patterns such as `array_contains_spec`.

The Coq helper only defines this task-specific spec and nothing else.

## Verification-friendly implementation form

Rewrite the loop guard from `while (s[i] != '\0')` to:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
}
```

This follows `doc/SCOPE.md` guidance for string scans and preserves the original semantics.
