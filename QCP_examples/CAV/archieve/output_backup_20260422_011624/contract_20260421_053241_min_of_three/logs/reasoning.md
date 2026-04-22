# Contract reasoning: min_of_three

## Source semantics

The raw problem asks for a function `min_of_three(a, b, c)` that returns the minimum of three integer inputs. The supplied implementation initializes `m` with `a`, then updates it with `b` and `c` when either is smaller.

Mathematically, the result must satisfy both parts of the problem statement:

- it is equal to one of the three original inputs;
- it is less than or equal to each original input.

These two clauses fully characterize the minimum among three scalar values, including ties.

## Interface and memory

The original interface is already verification-friendly:

```c
int min_of_three(int a, int b, int c)
```

There is no pointer, array, heap allocation, global state, or I/O. The contract therefore only needs scalar input-domain constraints and `emp` for the empty heap.

## Bounds and safety

The implementation only compares and assigns `int` values. It performs no arithmetic, so there is no additional overflow condition beyond the ordinary `int` input domain. The contract records each parameter in the `INT_MIN <= x <= INT_MAX` style used by nearby scalar examples such as `max_of_two`.

## Coq dependency judgment

No problem-specific Coq definition is needed. The postcondition can be expressed directly in the C contract using equality, disjunction, and order comparisons over the pre-state inputs.

Therefore `input/min_of_three.v` is not created.
