## Function semantics

Target function: `string_length`

The function scans a null-terminated character array starting at `s` and returns
the number of characters before the first `'\0'`. It does not modify memory.

## Interface and memory model

The raw statement says `s` points to a valid null-terminated character array.
In this repository, the standard representation for a C string is:

`CharArray::full(s, n + 1, app(l, cons(0, nil)))`

Here:

- `l` is the logical content of the string
- `n` is the logical length of `l`
- the allocated readable array has length `n + 1`
- the last byte is the terminating zero

Because the implementation only reads `s[i]` and never writes, the postcondition
should preserve the same `CharArray::full` assertion unchanged.

## Boundary conditions

- Empty string is allowed: `n = 0`, represented as a one-byte array containing only `0`
- Non-empty strings are allowed
- No extra value-range constraints on characters are needed
- The result is `n`

## Integer range judgment

The implementation uses `int i` and increments it until the terminator. To keep
the return value and index arithmetic verification-friendly, require `n < INT_MAX`.
This matches the common repository style for loop counters over logical lengths.

## Coq dependency judgment

No dedicated `input/string_length.v` is needed.

Reason:

- the repository already provides `CharArray::full`
- the desired semantic result is just `__return == n`
- no problem-specific logical wrapper or auxiliary mathematical definition is required

## Contract writing choice

Use a direct C contract with:

- `With l n`
- precondition `n < INT_MAX` plus the standard null-terminated string predicate
- postcondition `__return == n` and unchanged string ownership

Do not add Verify-stage material such as loop invariants or bridge assertions here.
