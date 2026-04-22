# Contract issues: string_has_double_char

## Resolved

- The raw implementation reads `s[1]` before checking whether the input is
  empty.  The generated contract input uses a semantically equivalent
  adjacent-pair scan for strings of length at least one, and additionally
  handles the intended valid empty-string case safely by returning `0`.

## Open

- None.
