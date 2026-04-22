# Issues: string_remove_char_to_output

No blocking issues.

Notes:

- The raw interface is already verification-friendly: `s`, `out`, and `c` are explicit parameters, and the caller provides the output buffer.
- The loop was rewritten from `while (s[i] != '\0')` to an explicit break-on-zero form for frontend stability without changing semantics.
- The postcondition fixes the output prefix as the filtered string followed by `0`; the unused suffix of the `n + 1` output buffer is existentially quantified.
- A problem-specific Coq file is required because the filtered-output list semantics is not available as an existing shared definition.
