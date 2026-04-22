## Semantic summary

Target function `array_reverse_in_place` takes an explicit array length `n` and a caller-owned integer array `a`. It reverses the array contents in place by swapping symmetric elements while moving `left` upward and `right` downward.

The mathematical result is the original logical list reversed: if the pre-state array contents are `l`, the post-state array contents are `rev(l)`.

## Contract decisions

- Keep the original interface. The function already receives the mutable buffer from the caller and does not allocate memory.
- Model `a` with `IntArray::full(a, n, l)` so the contract records both ownership and the pre-state element list.
- Add `0 <= n` to match the stated input domain and to make the `n - 1` initialization meaningful for the empty-array case.
- Add `Zlength(l) == n` so the logical list length is explicit and aligned with the concrete array length.
- Express the postcondition directly as `IntArray::full(a, n, rev(l))`. This captures the full in-place update while preserving ownership of the same buffer.

## Memory and bounds

- For `n == 0`, `right` is initialized to `-1`; the loop condition `left < right` is false, so no array access occurs.
- For `n == 1`, `right` is initialized to `0`; the loop is also skipped.
- When the loop body executes, `left < right` and the intended loop movement keeps both indices within `[0, n - 1]`, so the accesses `a[left]` and `a[right]` are within the owned array.
- The function performs no allocation and only mutates the supplied array cells.

## Coq dependency judgment

No `input/array_reverse_in_place.v` is needed. The repository list library already provides `rev`, and the whole functional result can be stated directly in the C contract without a task-specific Coq bridge.
