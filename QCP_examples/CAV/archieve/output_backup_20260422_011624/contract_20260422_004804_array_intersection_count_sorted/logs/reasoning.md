# Contract reasoning: array_intersection_count_sorted

## Source semantics

The target function scans two nondecreasing integer arrays with indices `i` and `j`.

- If `a[i] == b[j]`, the two occurrences are paired once, `count` is incremented, and both indices advance.
- If `a[i] < b[j]`, the current occurrence from `a` cannot pair with the current or any later element of `b`, so only `i` advances.
- If `a[i] > b[j]`, the symmetric case advances only `j`.

The return value is the multiset intersection cardinality of the two sorted input lists.

## Boundary conditions

- `n` and `m` may be zero.
- `a` owns a readable integer array of length `n`, abstracted as `la`.
- `b` owns a readable integer array of length `m`, abstracted as `lb`.
- `Zlength(la) == n` and `Zlength(lb) == m` connect logical list bounds to C array bounds.
- Both logical lists are nondecreasing, expressed directly in the C precondition with pairwise index ordering.

## Arithmetic and memory safety

The implementation does not mutate either array, so both `IntArray::full` resources are preserved in the postcondition.

The only integer increments are `i++`, `j++`, and `count++`. Preconditions include `n <= INT_MAX` and `m <= INT_MAX`; since `i <= n`, `j <= m`, and `count` is bounded by the number of paired occurrences, these are the intended overflow boundaries for Verify-stage invariants. No arithmetic over array element values is performed; elements are only compared.

## Coq dependency decision

The repository does not expose a ready-made public function for sorted multiset intersection count. The topic needs a small recursive list function that mirrors the two-pointer sorted scan. Therefore `input/array_intersection_count_sorted.v` is needed, containing only:

- `array_intersection_count_sorted_spec : list Z -> list Z -> Z`

No extra Coq precondition wrapper is needed because length, memory ownership, and sortedness are simple and readable in the C contract.
