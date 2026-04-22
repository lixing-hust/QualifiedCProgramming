## Semantics

Target function: `sum_to_n`.

The raw intent is a pure scalar computation: given an integer `n`, return the sum of all integers from `1` through `n`. The provided implementation uses a single loop with accumulator `ret`, and the problem statement explicitly allows `n == 0`, in which case the correct result is `0`.

## Boundary Conditions

- Require `0 <= n` to match the stated input domain.
- The implementation performs repeated integer addition, so the contract should constrain the mathematical final result to stay within the signed 32-bit range.
- For this problem, the natural closed form is `n * (n + 1) / 2`. Using that directly in the precondition is shorter and more stable than trying to constrain each intermediate loop state separately.
- Because the partial sums are monotone for `n >= 0` and never exceed the final sum, bounding the final closed form is enough to justify all loop additions at the contract stage.

## Memory Shape

The function does not read or write heap memory and only uses local scalar variables. Therefore both precondition and postcondition use `emp`.

## Postcondition Choice

The postcondition can be written directly as:

`__return == n@pre * (n@pre + 1) / 2`

This captures the intended mathematical result without introducing an extra logical wrapper. No `With` clause is needed because the postcondition only refers to the pre-state value of `n`.

## Coq Dependency Decision

No dedicated `input/sum_to_n.v` file is needed.

Reason:

- the problem is a basic integer arithmetic function,
- the semantics are expressible directly in the C contract,
- no problem-specific `pre/spec` bridge or auxiliary Coq definition is required.
