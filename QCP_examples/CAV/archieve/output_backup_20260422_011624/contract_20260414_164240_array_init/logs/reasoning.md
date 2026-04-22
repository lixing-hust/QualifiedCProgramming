# Reasoning

- Target function: `array_init`
- Raw task semantics: for a nonnegative integer `n` and a writable integer array `a` of length at least `n`, set `a[0]` through `a[n - 1]` to `0` and do not access elements outside that prefix.
- The function is an in-place array update, so the precondition must describe the existing writable array contents and the postcondition must describe the updated array contents after the prefix write.
- The repository already uses `IntArray::full(a, n, l)` for a readable/writable length-`n` integer array with abstract contents `l`, and it provides `zeros(n)` as the canonical all-zero list. That is enough to express this task directly in C without a task-specific Coq bridge.
- The contract therefore uses `With l` to bind the input array contents, `Require 0 <= n && IntArray::full(a, n, l)`, and `Ensure IntArray::full(a, n, zeros(n))`.
- No extra alias clause is needed because there is only one pointer argument. Nullability and bounds are handled through `IntArray::full(a, n, l)`: it gives the required writable contiguous memory for exactly the first `n` elements.
- No `.v` file is needed. The task does not require any custom mathematical relation beyond the existing array predicates and `zeros`.
- To stay within the annotate boundary, the output C contains only the verification-friendly function plus complete `Require` / `Ensure` clauses. It deliberately does not include loop invariants, `Assert`, `Inv`, bridge assertions, or `which implies` blocks.
- The implementation can remain the original `for` loop because it already matches the natural imperative structure of the task and does not need any semantic rewrite.
