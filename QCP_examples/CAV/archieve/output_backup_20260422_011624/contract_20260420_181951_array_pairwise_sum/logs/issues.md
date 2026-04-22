# Contract issues: array_pairwise_sum

## Open issues

None.

## Notes

- The contract requires separated ownership for `a`, `b`, and `out` through separating conjunction. This matches the verification-friendly interpretation of three distinct arrays supplied by the caller.
- Signed integer overflow is excluded by an explicit pointwise precondition on `la[i] + lb[i]`.
- No optional Coq file was generated because the postcondition is directly expressible in the C contract.
