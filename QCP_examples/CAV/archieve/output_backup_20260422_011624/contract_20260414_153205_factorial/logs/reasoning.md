# Reasoning

- Target function: `fac`
- Raw task semantics: compute the factorial of a nonnegative integer `n`, with `0 <= n <= 10`.
- The reference implementation is pure integer arithmetic with no heap effects, pointer arguments, aliasing, or mutable shared state. The contract therefore uses `emp` in both precondition and postcondition.
- The bound `n <= 10` must stay in the precondition because the raw markdown explicitly states that range and also says the reference implementation assumes the result fits in `int`. Keeping the bound in the contract is the conservative way to cover overflow risk while preserving the intended semantics.
- The result is exactly the mathematical factorial of the input. This is simple enough to express with direct `Extern Coq (factorial: Z -> Z)` rather than introducing a task-specific `.v` bridge.
- No `With` variables are needed because the function has no heap-shaped logical state and the postcondition can refer directly to `n@pre`.
- To stay within the annotate skill boundary, the output C should include only the function and complete `Require` / `Ensure` clauses. Loop invariants belong to Verify and should not be added here.
- The implementation can remain the same iterative loop because it is already verification-friendly and semantically equivalent to the raw code.
