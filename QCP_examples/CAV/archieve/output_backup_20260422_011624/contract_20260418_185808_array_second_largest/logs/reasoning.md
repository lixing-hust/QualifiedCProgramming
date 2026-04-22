## Semantic summary

- Target function scans an integer array once and returns the second-largest element.
- The raw statement already fixes the intended domain: `n >= 2`, array length is exactly `n`, all elements are pairwise distinct, and the array is read-only.
- The implementation only reads `a` and returns one existing array value; there is no semantic reason to change the interface.

## Contract design

- Keep the interface `int array_second_largest(int n, int *a)`.
- Use `With l` together with `IntArray::full(a, n, l)` so the contract exposes the full abstract array content and restores it unchanged in the postcondition.
- Require `2 <= n` and `Zlength(l) == n`.
- Encode the “all elements are distinct” assumption explicitly as a pairwise-distinct quantified precondition:
  `(forall (i: Z), (forall (j: Z), (0 <= i && i < n && 0 <= j && j < n && i != j) => l[i] != l[j]))`
- Postcondition should express only the final mathematical result, not loop-state facts.

## Coq dependency decision

- A task-specific `.v` file is needed.
- Reason: there is no obvious existing shared Coq function for “second largest of a nonempty distinct list with length at least 2”.
- The most verification-friendly definition is a recursive function mirroring the C scan: initialize from the first two elements, then update `(max1, max2)` while traversing the tail.

## Memory and safety notes

- `IntArray::full(a, n, l)` provides ownership of the whole readable array segment.
- The function does not write through `a`, so the postcondition restores the same `IntArray::full(a, n, l)`.
- Array accesses `a[0]`, `a[1]`, and `a[i]` are justified by `2 <= n` and the loop guard `i < n`.
- No arithmetic beyond comparisons, assignments, and bounded index progression is introduced.

## Interface rewrite decision

- No rewrite is needed.
- The original interface is already verification-friendly: one target function, explicit length parameter, no hidden allocation, no I/O, no global state.
