# Issues: array_longest_nonnegative_run

No blocking issues.

Notes:

- The raw interface is already verification-friendly, so no interface change was
  needed.
- A task-specific Coq file is required because the longest nonnegative-run list
  function is not available as an existing shared definition.
- The C output contains only the target function and its contract; no Verify-stage
  `Inv`, `Assert`, bridge assertion, or loop-exit assertion was added.
