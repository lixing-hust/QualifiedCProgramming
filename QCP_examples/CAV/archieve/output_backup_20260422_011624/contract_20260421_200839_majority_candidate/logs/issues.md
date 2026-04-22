# Issues: majority_candidate contract

## Blocking issues

None.

## Notes

- The original function interface is suitable for the contract workflow.
- The problem only requires the Boyer-Moore candidate, not a proof that the candidate is a true majority element.
- `input/majority_candidate.v` is necessary because the postcondition depends on a topic-specific candidate/count transition over the list contents.
