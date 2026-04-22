# Contract issues: array_reverse_in_place

## Open issues

None.

## Notes

- The original interface is verification-friendly: the caller supplies the mutable array and the function performs no allocation.
- The postcondition uses the existing list `rev` operation, so no optional Coq file was generated.
- Empty and singleton arrays are covered by `0 <= n` and the loop guard, with no memory access in either case.
