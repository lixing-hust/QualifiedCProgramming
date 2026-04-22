# Contract reasoning: partition_nonnegative

## Source semantics

The raw task defines `partition_nonnegative(int n, int *a)` over an integer array of exactly length
`n`. The function mutates the array in place so that every negative value is placed before every
nonnegative value, and returns the number of negative values in the final array. The task explicitly
does not require preserving the original relative order of elements.

The supplied implementation is a two-pointer partition:

- `i` scans and grows the negative prefix
- `j` bounds the unknown suffix from the right
- when `a[i] < 0`, `i` advances
- otherwise `a[i]` is swapped with `a[j]`, and `j` decreases
- when `i > j`, all positions before `i` are negative and all positions from `i` onward are
  nonnegative

The original interface is verification-friendly because the caller supplies the mutable array
buffer and the function has no side effects outside `a[0..n)`.

## Boundary and memory conditions

The natural input domain is `n >= 0`, with ownership of exactly the `n` integer cells in `a`. The
contract uses `IntArray::full(a, n, l)` to bind the initial contents and grant write permission over
the whole array.

An upper bound `n <= 2000` is included, matching nearby in-place array sorting contracts and keeping
loop counter arithmetic such as `n - 1`, `i + 1`, and `j - 1` in a verification-friendly signed-int
range. Array values are only compared and swapped, so no data-value overflow precondition is needed.

For `n = 0`, the implementation initializes `j` to `-1`, the loop is skipped, and the function
returns `0`; the final array segment remains empty.

## Postcondition choice

The postcondition describes the user-visible partition result, not any loop-specific intermediate
state:

- the return value is in `[0, n]`
- the final array contents `l0` are a permutation of the initial contents `l`
- every final index before `__return` contains a negative value
- every final index from `__return` to `n - 1` contains a nonnegative value
- ownership of the full array segment is returned with final contents `l0`

This directly implies that `__return` is the number of negative elements in the final array, while
allowing any order within the negative and nonnegative partitions.

## Coq dependency decision

The only extra logical predicate needed is Coq's standard list `Permutation`, already used by the
existing in-place sort contracts in this workspace. The partition shape can be expressed directly
with quantified index conditions in the C contract.

No task-specific Coq helper, wrapper predicate, or recursive specification is needed, so
`input/partition_nonnegative.v` should not be created.
