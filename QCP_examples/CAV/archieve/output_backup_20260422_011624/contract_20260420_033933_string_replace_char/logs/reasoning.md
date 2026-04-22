# Contract reasoning: string_replace_char

## Source semantics

The raw function scans a C-style null-terminated string from index `0` until it reaches the first `0` byte. For every scanned character, it writes `new_c` exactly when the original character equals `old_c`; otherwise it leaves the character unchanged. The terminating `0` byte is not modified.

For verification stability, the implementation is rewritten in the repository-preferred string-scan form:

- `while (1)`
- explicit `if (s[i] == 0) break;`
- integer `0` for the terminator

This preserves the source semantics.

## Contract shape

The contract models the input string as:

- a logical prefix list `l`
- a logical length `n`
- concrete memory `CharArray::full(s, n + 1, app(l, cons(0, nil)))`

Because the loop stops at the first `0`, the precondition must rule out interior terminators in the logical prefix:

- `forall k, 0 <= k < n -> l[k] != 0`

This makes the first encountered zero coincide with the final terminator in the modeled string.

The postcondition owns the same buffer with the transformed prefix and the original final terminator:

- `CharArray::full(s, n + 1, app(string_replace_char_spec(l, old_c, new_c), cons(0, nil)))`

The specification deliberately does not require the transformed prefix to remain nonzero, because `new_c` may be `0`.

## Bounds and memory

The scan index is an `int`, so the contract requires:

- `0 <= n`
- `n < INT_MAX`

The full writable ownership of `s[0..n]` is required because the function updates characters in place and reads the terminator.

## Coq dependency decision

A task-specific list transformer is needed to express conditional character replacement over the whole prefix. This is not a simple existing public Coq name, so `input/string_replace_char.v` is generated with:

- `replace_char`
- `string_replace_char_spec`

No verification-stage annotations are included in the contract output.
