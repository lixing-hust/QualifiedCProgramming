# Contract reasoning: majority_candidate

## Source semantics

The raw program implements the Boyer-Moore voting pass over a nonempty integer array.

Inputs:

- `n`: logical and concrete array length.
- `a`: pointer to an integer array of exactly `n` elements.

Preconditions from the problem statement:

- `n >= 1`.
- `a` has length exactly `n`.
- The function reads the array and does not modify it.

The function initializes:

- `candidate = a[0]`
- `count = 1`

It then scans indices `1` through `n - 1`. For each value `x = a[i]`:

- if `count == 0`, replace the candidate with `x` and reset `count` to `1`;
- else if `x == candidate`, increment `count`;
- otherwise decrement `count`.

The return value is the final candidate. The problem explicitly does not require checking that the candidate is a true majority element.

## Mathematical specification

The natural contract result is a deterministic list fold matching the Boyer-Moore state transition.

The specification is represented in `input/majority_candidate.v` by:

- `majority_candidate_step : Z -> Z -> Z -> Z * Z`
- `majority_candidate_acc : Z -> Z -> list Z -> Z`
- `majority_candidate_spec : list Z -> Z`

For a nonempty list `x :: xs`, `majority_candidate_spec` starts from candidate `x` and count `1`, then folds over `xs` using the same update as the C implementation.

Although the C precondition requires a nonempty list, the Coq function still gives `nil` a default result `0` so that the function is total.

## Contract shape

The C contract binds the logical contents of the array as `l`.

Required facts:

- `1 <= n`, matching the problem statement and making `a[0]` safe.
- `Zlength(l) == n`, connecting the logical list length to the concrete length.
- `IntArray::full(a, n, l)`, giving readable ownership of all elements.

Ensured facts:

- `__return == majority_candidate_spec(l)`, the final Boyer-Moore candidate.
- `IntArray::full(a, n, l)`, preserving the input array unchanged.

## Memory and mutation

The function only reads `a[i]`. It performs no writes through `a` and allocates no memory. Therefore the postcondition restores the exact same `IntArray::full(a, n, l)` predicate.

## Coq dependency decision

An extra `.v` file is needed because the output is the result of an algorithm-specific candidate/count transition over a list, and no existing public Coq function directly expresses this Boyer-Moore candidate semantics.

The `.v` file only contains the topic-specific total definitions needed by the C contract. No verification-stage invariants, assertions, or helper lemmas are included.

## Interface decision

The original interface is already verification-friendly:

```c
int majority_candidate(int n, int *a)
```

No interface rewrite is needed.
