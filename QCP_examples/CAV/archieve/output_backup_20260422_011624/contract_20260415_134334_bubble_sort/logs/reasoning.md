# bubble_sort annotate reasoning

## Inputs

- Raw statement: `raw/bubble_sort.md`
- Target function: `bubble_sort`
- Required outputs:
  - `input/bubble_sort.c`
  - optional `input/bubble_sort.v`

## Semantic understanding

The raw task asks for in-place bubble sort on an integer array of length `n`, producing nondecreasing order and using only swaps inside the original array. The implementation has no return value, so the entire semantic effect is captured as a postcondition over the final array contents.

## Boundary and safety choices

- Keep the algorithm unchanged. The given implementation is already verification-friendly imperative C.
- Preserve the input bound `0 <= n <= 2000` from the statement.
- Use `IntArray::full(a, n, l)` as the ownership and writable-memory predicate for the whole array.
- No extra overflow precondition is needed for element values because the code only compares and swaps existing `int` values; it does not perform arithmetic that can overflow.
- No separate null-pointer clause is needed beyond `IntArray::full(a, n, l)`, which already captures the memory shape for `n` elements.

## Spec shape

The postcondition needs two properties:

1. The final abstract list is sorted in nondecreasing order.
2. The final abstract list is a permutation of the initial abstract list.

This is more precise than a shape-only spec and matches the raw problem statement.

## Coq dependency decision

The repository already uses `Permutation` in existing specs, but there is no local `CAV/input` bridge for an array-sorting predicate over `list Z`. A small task-specific `.v` file is therefore justified.

Planned logic names:

- `sorted_z : list Z -> Prop`
- `Permutation : list Z -> list Z -> Prop`

`sorted_z` will be defined in `input/bubble_sort.v` as a simple recursive nondecreasing predicate. `Permutation` will be imported from Coq's standard library rather than redefined.

## Annotate/Verify separation check

The output C file should contain only:

- includes
- `Extern Coq` / `Import Coq`
- function definition
- `With` / `Require` / `Ensure`

It must not contain loop invariants, asserts, bridge asserts, `which implies`, or exit assertions.
