# Contract reasoning: house_robber

## Source semantics

The raw task defines `house_robber(int n, int *a)` for an array `a` of length `n`.
The function returns the maximum sum obtainable by selecting array elements with no two selected elements adjacent.

The implementation is the standard rolling dynamic program:

- `prev2` is the optimal value two positions back.
- `prev1` is the optimal value one position back.
- each iteration computes `cur = max(prev2 + a[i], prev1)`.
- then the rolling state advances with `prev2 = prev1` and `prev1 = cur`.

For `n == 0`, the loop body is skipped and the result is `0`.

## Interface decision

The original interface is already verification-friendly:

- one target function;
- no I/O or global state;
- no allocation;
- input array is read but not modified.

The C implementation is preserved.

## Mathematical specification

No existing public Coq function was identified that directly states the house-robber no-adjacent maximum.  A problem-specific file `input/house_robber.v` is therefore needed.

The Coq specification mirrors the mathematical rolling recurrence:

```coq
house_robber_acc prev2 prev1 l
```

returns the result after scanning the remaining list `l` with rolling states `prev2` and `prev1`.

The public specification is:

```coq
house_robber_spec l := house_robber_acc 0 0 l
```

This captures the empty-array result `0` and the usual recurrence for all nonempty lists.

## Preconditions

The contract requires:

- `0 <= n && n <= INT_MAX`;
- `Zlength(l) == n`;
- every element is nonnegative;
- `sum(l) <= INT_MAX`;
- `IntArray::full(a, n, l)`.

The nonnegative-element and sum bound match the problem statement and provide a compact overflow bound.  Since every DP value is bounded by the sum of a nonnegative prefix, `prev2 + a[i]` and all stored DP values remain within signed `int` range when the total sum is at most `INT_MAX`.

## Postconditions

The postcondition states:

- the return value equals `house_robber_spec(l)`;
- the array footprint is restored as `IntArray::full(a, n, l)`.

The array footprint in the postcondition records that the function does not modify `a`.

## Verify-stage exclusions

No loop invariants, `Assert`, bridge assertions, implication hints, or loop-exit assertions are included in the contract output.  These belong to the Verify stage.
