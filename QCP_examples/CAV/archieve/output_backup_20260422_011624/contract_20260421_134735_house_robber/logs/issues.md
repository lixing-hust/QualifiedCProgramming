# Contract issues: house_robber

No unresolved contract issues.

## Notes

- The original interface was suitable for verification and was preserved.
- A problem-specific Coq helper was created because the no-adjacent maximum DP semantics are not a simple existing public function.
- The overflow precondition uses nonnegative inputs plus `sum(l) <= INT_MAX`, which is enough for the rolling DP arithmetic because all intermediate values are bounded by the total input sum.
