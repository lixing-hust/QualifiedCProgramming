## Function

`abs_value(int x)` returns the mathematical absolute value of `x`.

## Semantic Decision

- Preserve the original interface and branch structure.
- No interface rewrite is needed: the function is pure, scalar-only, and has no memory effects.
- The only essential domain restriction is `x != INT_MIN`, because `-INT_MIN` overflows signed 32-bit `int`.

## Contract Shape

- `Require` should exclude `INT_MIN`.
- `Ensure` should express the result in a branch-independent way:
  - return value is nonnegative
  - return value equals either `x@pre` or `-x@pre`
- This matches the raw statement and avoids introducing verify-stage assertions.

## Memory / Ownership

- The function reads only its scalar argument.
- No heap, pointer, array, or buffer predicate is needed.
- Use `emp` in both precondition and postcondition.

## Coq Dependency Judgment

- No custom `.v` file is needed.
- The postcondition can be written directly in C contract syntax without a dedicated Coq wrapper.
- No existing public Coq function is necessary for this specification.
