# Issues: binary_search_first Contract

## Resolved

- The raw task already used a verification-friendly interface: one scalar length, one input array, and one scalar target.
- No interface rewrite was needed.
- No extra Coq definitions were needed because the first-match semantics are expressible directly in the C contract.

## Open Issues

- None.

## Notes for Verify

- The contract intentionally does not include loop invariants, assertions, bridge assertions, or loop-exit assertions.
- The postcondition captures first occurrence by requiring every earlier element to differ from `target` when the return value is a valid index.
