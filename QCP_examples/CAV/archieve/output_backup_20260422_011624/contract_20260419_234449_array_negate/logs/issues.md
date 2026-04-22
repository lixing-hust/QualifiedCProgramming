# Contract Issues: array_negate

No blocking issues.

Notes:

- The original implementation and interface are verification-friendly and were preserved.
- The contract adds a signed-int overflow precondition for unary negation, excluding `INT_MIN`.
- No task-specific Coq bridge file is needed.
