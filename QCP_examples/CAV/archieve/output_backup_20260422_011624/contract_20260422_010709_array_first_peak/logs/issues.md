# Contract issues: array_first_peak

No blocking issues.

Notes:

- The original interface is verification-friendly and was kept unchanged.
- No task-specific Coq bridge file is required.
- The postcondition uses the expanded non-peak condition
  `l[i] < l[i - 1] || l[i] < l[i + 1]` instead of a negated conjunction.
