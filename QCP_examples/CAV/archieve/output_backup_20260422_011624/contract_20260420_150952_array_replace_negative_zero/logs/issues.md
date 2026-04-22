# Contract issues: array_replace_negative_zero

No blocking issues.

Notes:

- The raw interface was kept unchanged.
- No additional Coq dependency file is required.
- No overflow precondition is needed because the function only compares values
  with `0` and assigns `0`.
