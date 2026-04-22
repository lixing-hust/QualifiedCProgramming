No blocking issues.

Decisions:

- Kept the original interface unchanged.
- Used `CharArray::undef_full(s, n + 1)` instead of requiring prior contents.
- Did not create `input/string_set_a.v` because `repeat_Z` is already sufficient.
