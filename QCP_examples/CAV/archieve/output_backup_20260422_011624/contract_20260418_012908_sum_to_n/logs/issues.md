No blocking issues.

Decisions recorded:

- kept the original interface unchanged,
- did not create `input/sum_to_n.v` because the semantics are expressible directly in the C contract,
- used the closed-form overflow bound `n * (n + 1) / 2` in the precondition instead of encoding loop-level reasoning in Contract.
