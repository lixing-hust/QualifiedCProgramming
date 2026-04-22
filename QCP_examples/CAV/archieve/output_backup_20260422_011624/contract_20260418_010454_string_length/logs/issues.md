No blocking issues.

Decisions:

- Kept the original interface `int string_length(char *s)`
- Did not create `input/string_length.v` because the repository’s existing string predicates are sufficient
- Added `n < INT_MAX` to support the `int` loop counter and return value
