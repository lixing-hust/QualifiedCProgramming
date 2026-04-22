# Contract Reasoning: max_of_three

## Source semantics

The raw task defines `max_of_three(a, b, c)` as a pure scalar function returning the maximum of three integer inputs.

The implementation initializes `m` with `a`, updates it to `b` when `b > m`, updates it to `c` when `c > m`, and returns `m`.

## Boundary conditions

- Inputs are ordinary C `int` values.
- The function performs only comparisons and assignments.
- There is no arithmetic, so no additional arithmetic overflow precondition is needed beyond the standard `int` range assumptions used by local examples.
- Equal inputs are allowed.
- The returned value must be one of the original inputs and must be greater than or equal to all original inputs.

## Memory model

The function has no pointer parameters, no heap allocation, and no global state. The footprint is `emp` in both precondition and postcondition.

## Coq dependency judgment

No problem-specific Coq definition is required. The postcondition can be expressed directly in the C contract with equality, disjunction, and ordering over `a@pre`, `b@pre`, `c@pre`, and `__return`.

Therefore `input/max_of_three.v` is not needed.

## Contract shape

The contract follows the existing scalar style used by `input/max_of_two.c` and `input/min_of_three.c`:

- `Require`: each argument is within `INT_MIN` and `INT_MAX`, plus `emp`.
- `Ensure`: the return value is one of the three pre-state arguments and is at least each pre-state argument, plus `emp`.
