# Contract Issues: array_count_transitions

No blocking issues.

## Decisions

- Kept the original function interface because it is already a single pure array-scanning function.
- Added a task-local Coq specification file because the repository did not have an existing public adjacent-transition-count function.
- Used a helper recursive function in Coq so the definition is structurally accepted.
- Preserved the original C implementation without verification-stage annotations.

## Residual risk

The Verify stage will still need loop invariants connecting `cnt` to the transition count of the processed prefix. That is expected Verify-stage work and is not encoded in the contract.
