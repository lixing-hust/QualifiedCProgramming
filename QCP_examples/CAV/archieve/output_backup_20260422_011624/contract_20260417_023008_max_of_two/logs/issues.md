No blocking issues.

Decisions:

- Kept the original interface unchanged.
- Did not generate `input/max_of_two.v` because the semantics are expressible directly in the C contract.
- Used a relational postcondition instead of an `Extern Coq` max function to keep the contract minimal.
