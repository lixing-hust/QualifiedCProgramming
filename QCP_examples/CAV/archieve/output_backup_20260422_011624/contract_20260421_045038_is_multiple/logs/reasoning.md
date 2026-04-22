# Contract Reasoning: is_multiple

## Source Semantics

The raw task defines `is_multiple(a, b)` for an integer `a` and a positive integer `b`.
The function returns `1` exactly when `a % b == 0`; otherwise it returns `0`.

The original implementation is already verification-friendly:

- single scalar target function
- no pointers or heap ownership
- no loops
- no I/O or global state
- no interface rewrite needed

## Preconditions

The only semantic precondition required by the task and by C modulo safety is:

- `b > 0`

No additional bounds are needed because the implementation does not perform arithmetic that can overflow; `%` is defined for any `int a` when the divisor is nonzero.

## Postconditions

The result is a boolean encoded as an integer:

- return `1` when `a@pre % b@pre == 0`
- return `0` when `a@pre % b@pre != 0`

This also fully captures the promised return range `{0, 1}`.

## Memory

The function has no memory arguments and no heap effects, so both precondition and postcondition use `emp`.

## Coq Dependencies

No problem-specific Coq definition is needed. The specification can be expressed directly with integer modulo in the C contract, so `input/is_multiple.v` should not be created.
