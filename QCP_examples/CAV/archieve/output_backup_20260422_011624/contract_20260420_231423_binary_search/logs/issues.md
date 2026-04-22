# Contract issues: binary_search

## Resolved

- The raw statement permits returning any matching index, so the postcondition uses an arbitrary valid matching index rather than a first-occurrence or last-occurrence spec.
- The empty-array case is covered by `n >= 0` and the failure postcondition; no special implementation rewrite was needed.
- No task-specific Coq file was created because the specification is expressible directly in the C contract.

## Open issues

- None.
