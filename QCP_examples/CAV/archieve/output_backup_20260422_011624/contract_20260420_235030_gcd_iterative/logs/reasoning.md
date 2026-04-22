# Contract Reasoning: gcd_iterative

## Source Semantics

- Target function: `gcd_iterative`.
- Inputs: two nonnegative integers `a` and `b`.
- Problem constraint: `a` and `b` are not both `0`.
- The implementation is the standard iterative Euclidean algorithm:
  - while `b != 0`, compute `r = a % b`;
  - assign `a = b` and `b = r`;
  - return the final `a`.

## Boundary Cases

- `a > 0, b == 0`: the loop is skipped and the function returns `a`, which is the gcd.
- `a == 0, b > 0`: the first iteration computes `0 % b == 0`, then returns the original `b`.
- `a > 0, b > 0`: Euclid's key property is that the gcd of the current pair is the same as the gcd of the original pair.
- `a == 0, b == 0` is excluded by the problem statement and by the contract.

## Arithmetic and Memory

- The function uses only scalar integer variables and has no heap or pointer memory.
- The modulo operation is executed only when `b != 0`, so division by zero is avoided by the loop guard.
- For nonnegative inputs, C remainder values stay nonnegative and strictly smaller than the divisor when the divisor is positive.
- No addition or multiplication occurs, so there is no extra arithmetic overflow bound beyond the nonnegative input domain.

## Result Specification

The natural semantic postcondition is that the returned value is the greatest common divisor of the original inputs.

The C contract will use a task-specific Coq predicate:

- `gcd_iterative_spec(a@pre, b@pre, __return)`

The predicate is defined as equality with Coq's standard nonnegative integer gcd:

- `r = Z.gcd a b`

## Coq Dependency Decision

- No existing local public `gcd` wrapper was found in the CAV tree.
- Directly exposing a dotted stdlib name such as `Z.gcd` through `Extern Coq` is less stable than a small task-local wrapper.
- Create `input/gcd_iterative.v` with only the task-specific predicate `gcd_iterative_spec`.

## Verify-Stage Boundary

- Do not add Verify-stage proof annotations in Contract output.
- The C file should contain only the target function and its complete `Require` / `Ensure` contract.
