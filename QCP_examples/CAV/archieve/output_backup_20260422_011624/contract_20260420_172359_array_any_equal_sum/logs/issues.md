# Contract Issues: array_any_equal_sum

No blocking issues.

Notes:

- The implementation computes `x + y` in C before scanning the array, so the contract includes `INT_MIN <= x + y && x + y <= INT_MAX`.
- No task-specific Coq definitions are required.
