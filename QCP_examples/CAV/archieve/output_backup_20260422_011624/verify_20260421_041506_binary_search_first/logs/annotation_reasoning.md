# Annotation Reasoning

## Round 1

- Current program point: the only loop is `while (left < right)` in `annotated/verify_20260421_041506_binary_search_first.c`. The active annotated copy currently matches the input and has no loop invariant, so symbolic execution would not have a summary connecting `left`, `right`, the sorted list `l`, and the first-occurrence postcondition.
- Loop state meaning:
  - `left` is the first index not yet proven to contain a value strictly less than `target`.
  - `right` is the first index of the suffix already proven to contain values at least `target`.
  - the active search interval is the half-open range `[left, right)`.
  - every `j < left` has been excluded because `l[j] < target`, which is stronger than `l[j] != target` and is exactly what is needed for the first-occurrence branch.
  - every `right <= j < n` has been excluded from the lower half because `l[j] >= target`.
- Required postcondition:
  - if the function returns a nonnegative index, it must be in range, the array value at that index must equal `target`, and all earlier positions must be unequal to `target`;
  - if the function returns `-1`, every in-range array value must be unequal to `target`;
  - the input array memory must remain `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= right`, `right <= n`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts needed after each branch: `n <= INT_MAX`, `Zlength(l) == n`, and the global sortedness fact from the precondition;
  - excluded-region facts:
    - `(forall (j: Z), (0 <= j && j < left) => l[j] < target)`;
    - `(forall (j: Z), (right <= j && j < n) => l[j] >= target)`;
  - empty-interval point fact `((left == right && left < n) => l[left] >= target)`, matching the lower-bound example and giving the exit state a direct fact about `left` when it is in range;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n`. Both excluded regions are empty, and the point fact is vacuous because `left == right` only when `n == 0`, making `left < n` false.
- Preservation expectation:
  - after `mid = left + (right - left) / 2`, the active loop condition `left < right` should imply `left <= mid`, `mid < right`, and therefore `0 <= mid < n`; add a bridge assertion before reading `a[mid]`.
  - in the `a[mid] < target` branch, sortedness implies every old candidate index up to `mid` is also below target, so assigning `left = mid + 1` extends the strict-less prefix.
  - in the `else` branch, the failed comparison gives `l[mid] >= target`; sortedness extends this to the suffix after assigning `right = mid`.
- Exit usefulness: when the loop exits, `left == right`. If the final `if` returns `left`, the prefix invariant proves first occurrence. If it returns `-1`, either `left == n` and the strict-less prefix covers the whole array, or `left < n` and `l[left] != target` plus sortedness and the suffix facts show no later element equals target.

## Planned edit

- Add the half-open binary-search invariant immediately before the loop.
- Add a midpoint bridge assertion immediately after computing `mid`.
- Add a branch bridge assertion in the `else` branch before `right = mid`, carrying `l[mid] >= target` and the invariant facts needed for preservation.
