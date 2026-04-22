# Annotation Reasoning

## Semantic understanding

`bubble_sort` mutates the input array `a` in place. The outer loop counts how many largest elements have been moved to the suffix. The inner loop scans the still-unsorted prefix and swaps adjacent entries when they are out of order.

The contract is already fixed by the input and should not be rewritten in verify. The verification task is therefore to preserve full ownership of the array through both loops and to expose enough loop structure for symbolic execution to generate sensible obligations for sortedness and permutation.

## Why these invariants

The first pass will use conservative invariants:

- Outer loop: keep bounds on `i`, keep `a` and `n` stable relative to `@pre`, and preserve `IntArray::full(a, n, l_outer)` for some current logical list `l_outer`.
- Inner loop: keep bounds on `i` and `j`, keep `a` and `n` stable, preserve `IntArray::full(a, n, l_inner)` for some current logical list `l_inner`, and relate the inner loop bound to `n - i`.

This is the minimum shape information needed to justify repeated reads and writes to `a[j]` and `a[j + 1]` while letting `symexec` show whether stronger semantic information is needed for the final sortedness/permutation proof.

## Candidate strengthening if needed

If the first symbolic run cannot connect loop exits to the final postcondition, the likely next strengthening is:

- outer loop records that the suffix `[n - i, n)` is already sorted and contains the `i` largest elements of the current permutation;
- inner loop records that after scanning up to `j`, the maximum of the processed prefix has bubbled to position `j`.

That stronger form would require either additional Coq-side helper predicates/functions or more explicit list-segment relations in the annotations.

## Risks checked up front

- Bounds: `0 <= n <= 2000` is enough for the loop indices to stay within the array domain when `j + 1 < n - i`.
- Aliasing: the function only touches the single owned array block `a`; there are no extra pointers.
- Overflow: the code only compares, loads, stores, and swaps `int` values; there is no arithmetic on array elements beyond index arithmetic.
- Exit reasoning: because there are two nested loops, an explicit loop-exit assertion may be needed after the inner loop or outer loop if the generated witness leaves the exit condition implicit.
