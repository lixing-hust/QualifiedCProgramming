# bubble_sort annotate issues

## Decisions and tradeoffs

- Chose a semantic postcondition over the full array contents instead of a shape-only spec, because the task explicitly requires sorting.
- Kept the original bubble-sort implementation unchanged. It already avoids platform I/O, heap allocation, and auxiliary wrappers.
- Added a task-specific `input/bubble_sort.v` because the repo did not expose a ready-to-use local sorted-array predicate for `list Z` in `CAV/input`.

## Rejected alternatives

- Did not weaken the postcondition to only `IntArray::full_shape(a, n)`. That would miss the core sortedness guarantee.
- Did not encode the full contract purely in C without `.v`; `sorted_z` needs a logic definition.
- Did not introduce verify-stage loop invariants or bridge assertions. Those belong to the later Verify phase.

## Risks to watch in Verify

- The later proof will need lemmas connecting adjacent swaps with `Permutation`.
- The recursive `sorted_z` predicate is intentionally simple, but Verify may still need standard list lemmas to reason about suffix ordering after each pass.
