# Issues: string_count_not_char

## Resolved

- The raw loop used `while (s[i] != '\0')`; the contract output uses the repository-preferred `while (1)` plus explicit zero check form for frontend stability.
- The string precondition includes an explicit no-internal-zero condition so the logical payload `l` matches the characters scanned before termination.
- A task-specific Coq spec was added because the count-not-equal semantics is content-dependent and not directly available as a public reusable definition.

## Open

- None.
