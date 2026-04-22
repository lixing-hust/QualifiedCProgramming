# Issues: string_ends_with_char

## Resolved

- The raw implementation used `'\0'`; the generated verification input uses integer `0` for terminators, matching local string-contract guidance.
- The raw loop condition `while (s[i + 1] != '\0')` was rewritten as `while (1)` with an explicit break on `s[i + 1] == 0`, preserving behavior while matching the verification-friendly scanning style.
- The string contract explicitly excludes internal terminators in `l`, so the final character `l[n - 1]` is well aligned with the implementation's first-terminator scan.

## Open

- None.

## Optional Coq file

- `input/string_ends_with_char.v` was not created because the postcondition can be expressed directly in the C contract.
