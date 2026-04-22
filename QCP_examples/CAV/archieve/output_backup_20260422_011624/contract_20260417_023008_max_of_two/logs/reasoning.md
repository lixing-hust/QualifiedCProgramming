## Target

- Function: `max_of_two`
- Raw spec source: `raw/max_of_two.md`
- Output C: `input/max_of_two.c`
- Optional V: `input/max_of_two.v`

## Semantic Reading

The function takes two `int` inputs `a` and `b` and returns the larger one.

The intended behavior is:

- if `a >= b`, return `a`
- otherwise, return `b`

The function is pure with respect to memory: it reads only scalar parameters and does not modify heap or caller memory.

## Interface Judgment

The existing interface is already verification-friendly:

- scalar inputs only
- scalar return value
- no pointer ownership
- no loops
- no helper state

No interface rewrite is needed.

## Boundary Analysis

Inputs are C `int`, so the natural domain is:

- `INT_MIN <= a <= INT_MAX`
- `INT_MIN <= b <= INT_MAX`

There is no arithmetic that can overflow:

- the code only compares `a` and `b`
- the return value is exactly one of the inputs

Because the result is one of the inputs, the postcondition can state both:

- `__return == a@pre || __return == b@pre`
- `__return >= a@pre && __return >= b@pre`

This captures both the selection property and the maximality property without introducing extra Coq definitions.

## Memory Judgment

No heap memory is involved. The separation-logic footprint is `emp` in both precondition and postcondition.

## Coq Dependency Judgment

No extra `input/max_of_two.v` file is needed.

Reason:

- the semantics are simple enough to express directly in C contract form
- no reusable or custom mathematical function is required
- no custom `pre/spec` bridge improves clarity here

## Contract Shape Decision

Use a direct contract on the function:

- precondition: scalar inputs are valid `int` values and footprint is `emp`
- postcondition: result equals one of the original inputs and is greater than or equal to both original inputs, with footprint `emp`

This preserves the original branch structure and avoids introducing Verify-stage annotations.
