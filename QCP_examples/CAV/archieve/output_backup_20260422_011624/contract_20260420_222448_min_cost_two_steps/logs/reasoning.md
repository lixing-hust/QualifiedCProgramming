# Contract Reasoning: min_cost_two_steps

## Source Semantics

The raw function receives an integer `n` and an integer array `cost` of length `n`.
The caller starts at index `0`, may move forward by one or two indices, pays
`cost[i]` when entering index `i`, and must reach index `n - 1`.

The implementation is the standard two-state dynamic program:

- `opt[0] = cost[0]`
- `opt[1] = cost[0] + cost[1]`
- for `i >= 2`, `opt[i] = min(opt[i - 1], opt[i - 2]) + cost[i]`
- return `opt[n - 1]`

The input array is read-only and is restored unchanged in the postcondition.

## Boundary Conditions

The problem states `n >= 1`; the contract keeps this requirement. A practical
upper bound `n <= 10000` is added to match the style of existing array examples.
The array length is captured by `Zlength(l) == n`.

For `n == 1`, the function returns `cost[0]`, which matches the Coq definition.
For `n >= 2`, the accumulator definition starts from the first two DP states and
folds over the remaining list.

## Memory

The contract uses:

- `IntArray::full(cost, n, l)` in the precondition
- `IntArray::full(cost, n, l)` in the postcondition

This expresses that `cost` has exactly `n` integer cells, all values are modeled
by `l`, and the function does not modify the array.

## Integer Safety

All costs are constrained to be nonnegative. The contract also requires
`sum(l) <= 2147483647`. Since every DP value is the sum of a subset/path of
nonnegative costs, each stored DP state and each addition performed by the
implementation is bounded above by `sum(l)`, so the implementation stays within
signed 32-bit integer range.

The nonnegativity condition also implies each individual `l[i]` is within the
same upper bound under the total-sum constraint.

## Coq Dependency

The repository does not expose an existing Coq function for this exact path-cost
recurrence, so `input/min_cost_two_steps.v` is needed. It defines:

- `min_cost_two_steps_acc`, mirroring the loop over the tail of the cost list
- `min_cost_two_steps_z`, the public list-level specification used by the C
  contract

No additional pre/spec wrapper is needed because the C contract can express the
input domain and memory shape directly.
