# Contract reasoning: selection_sort

## Source semantics

The raw task defines `selection_sort(int n, int *a)` over an integer array of exactly length `n`.
The function sorts the array in place into nondecreasing order. It has no return value and no
side effects outside the array segment `a[0..n)`.

The supplied implementation is the standard selection sort:

- for each position `i`, find an index `min_idx` in the suffix `i..n-1` whose value is minimal
- swap `a[i]` with `a[min_idx]`
- continue until every position has been selected

The original interface is already verification-friendly: the caller supplies the array buffer,
and the function mutates it in place.

## Boundary and memory conditions

The natural input domain is `n >= 0`, with `a` owning exactly `n` integer cells. The contract uses
`IntArray::full(a, n, l)` to bind the initial contents `l` and to give the function write
permission over the full segment.

An upper bound `n <= 2000` is included to match existing array-sort contracts in this workspace and
to keep integer loop counters and simple arithmetic expressions within a verification-friendly
range. The implementation only increments loop counters up to `n`, so no additional data-value
overflow precondition is needed because array values are only compared and swapped.

For `n = 0`, the array segment is empty, both loops are skipped, and the postcondition is satisfied
by the empty output list.

## Postcondition choice

The user-visible sorting semantics is expressed as:

- the final array contents `l0` are nondecreasing
- `l0` is a permutation of the initial contents `l`
- the array still owns exactly the length-`n` full segment with contents `l0`

This avoids exposing algorithm-specific details such as selected minima or sorted prefixes in the
function contract. Those details belong to the Verify stage as invariants or assertions, not to the
Contract output.

## Coq dependency decision

The contract needs two logical predicates:

- `Permutation` from Coq's list permutation library
- `sorted_z`, a list-of-`Z` nondecreasing predicate

`Permutation` can be imported directly from the Coq standard library through the task `.v` file.
The workspace already uses a task-specific `sorted_z` definition for `bubble_sort`; however, to keep
`selection_sort` self-contained and avoid depending on another problem's module, this task should
create `input/selection_sort.v` with the same small `sorted_z` definition and import it from
`input/selection_sort.c`.

No additional problem-specific pre/spec wrapper is needed.
