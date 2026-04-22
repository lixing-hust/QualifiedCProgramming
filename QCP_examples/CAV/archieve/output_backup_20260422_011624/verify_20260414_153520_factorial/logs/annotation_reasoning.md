# Annotation Reasoning

## Function understanding

The function `fac` computes the factorial of a nonnegative integer `n` by maintaining an accumulator `res` and multiplying it by each integer `i` from `1` through `n`.

The input contract is already fixed and trusted:

- `0 <= n <= 10`
- postcondition `__return == factorial(n@pre)`

The bound `n <= 10` is sufficient to avoid `int` overflow for the concrete implementation.

## Annotation plan

The loop should track the product of all integers that have already been processed. For a `for (i = 1; i <= n; ++i)` loop, the clean invariant is:

- `1 <= i <= n + 1`
- `n == n@pre`
- `res == factorial(i - 1)`

This matches the operational meaning of the loop:

- before the first iteration, `i == 1` and `res == 1 == factorial(0)`
- at the start of an iteration, `res` is the factorial of the previous index
- after `res = res * i`, we expect `res == factorial(i)`
- after the loop increment, the invariant is restored as `res == factorial((i + 1) - 1)`

## Bridge assertions

Two bridge points are useful.

Before the multiplication in the body, record the current invariant together with the loop guard:

- `1 <= i <= n@pre`
- `res == factorial(i - 1)`

After the multiplication, record:

- `1 <= i <= n@pre`
- `res == factorial(i)`

These assertions make the preservation argument explicit and should produce a small arithmetic/factorial witness for Coq.

After loop exit, record:

- `i == n@pre + 1`
- `res == factorial(n@pre)`

This bridges the invariant plus negated guard to the function postcondition.

## Risks checked

- No heap or aliasing obligations beyond `emp`.
- No null-pointer or memory-shape reasoning is needed.
- The only nontrivial proof step should be the factorial recurrence used in the loop body.
