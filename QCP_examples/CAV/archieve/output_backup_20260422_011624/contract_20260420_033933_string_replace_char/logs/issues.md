# Issues: string_replace_char contract

## Resolved

- The raw loop condition `while (s[i] != '\0')` was rewritten to the verification-stable `while (1)` plus explicit zero check and `break`.
- The input string contract includes the no-interior-zero premise required for scans that stop at the first terminator.
- The postcondition does not require a no-zero transformed prefix, because `new_c` may be `0`.

## Open

- None.
