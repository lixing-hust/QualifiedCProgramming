# Contract issues: array_count_greater_than_k

## Issues

- No blocking issues.

## Notes

- The contract uses a task-specific Coq fixpoint because no reusable public definition for threshold-greater-than counting was found.
- The implementation is unchanged from the raw code except for adding the required includes and contract annotations.
- No Verify-stage annotations were added.
