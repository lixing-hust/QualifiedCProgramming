# Contract Reasoning: string_all_digits

## Source semantics

The raw program scans a valid C string from index `0` until the first `0`
terminator. It returns `0` immediately when it sees a character outside the
ASCII digit range `'0'..'9'`, and returns `1` after reaching the terminator.
The empty string returns `1` because the loop body is skipped.

## Verification-facing interface

The original interface `int string_all_digits(char *s)` is suitable for the
contract stage. The implementation is rewritten only superficially into a
verification-friendly `while (1)` loop with an explicit `if (s[i] == 0) break`.
ASCII digit constants are written as integers `48` and `57` to avoid frontend
noise from character constants.

## Input model and memory

Use a logical list `l` and length `n` for the non-terminator prefix:

- `0 <= n && n < INT_MAX` bounds the scan index and the allocated string length.
- `CharArray::full(s, n + 1, app(l, cons(0, nil)))` gives read access to the
  full C string including the terminator.
- `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` rules out internal
  terminators in the prefix, so the loop's first `0` is exactly the final
  terminator represented by `n`.

The function does not write to `s`, so the postcondition restores the same
`CharArray::full` predicate.

## Result semantics

The postcondition states `__return == string_all_digits_spec(l)`, where the
Coq function returns `1` iff every element of `l` is between `48` and `57`
inclusive, and returns `0` otherwise. This captures the empty-string case
directly because the Coq function maps `nil` to `1`.

## Coq dependency decision

A small task-specific Coq definition is useful because the semantic result is a
recursive predicate over a list. Therefore `input/string_all_digits.v` is
created with only `string_all_digits_spec`; no extra proof-stage definitions,
invariants, or assertions are added.
