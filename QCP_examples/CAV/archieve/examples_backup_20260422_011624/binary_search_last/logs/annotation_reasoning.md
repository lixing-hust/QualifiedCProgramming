# Annotation Reasoning

## Round 1 - 2026-04-21 04:27:25 +0800

- Current program point: the only loop is `while (left < right)` in `annotated/verify_20260421_042558_binary_search_last.c`. The active annotated copy currently matches the input and has no loop invariant, so symbolic execution has no summary for the binary-search interval or for proving the last-occurrence postcondition after the loop.
- Loop state meaning:
  - `left` is the first index not yet proven to have value `<= target`.
  - `right` is the first index of the suffix already proven to have value `> target`.
  - the active candidate interval is the half-open range `[left, right)`.
  - every `j < left` has `l[j] <= target`.
  - every `right <= j < n` has `l[j] > target`.
- Required postcondition:
  - when the final branch returns `left - 1`, that element must equal `target`, be in range, and every later element must not equal `target`;
  - when the function returns `-1`, every in-range element must be unequal to `target`;
  - array ownership remains `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= right`, and `right <= n`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts needed by preservation and exit reasoning: `n <= INT_MAX`, `Zlength(l) == n`, and global sortedness of `l`;
  - excluded-region facts:
    - `(forall (j: Z), (0 <= j && j < left) => l[j] <= target)`;
    - `(forall (j: Z), (right <= j && j < n) => l[j] > target)`;
  - empty-interval point fact `((left == right && left < n) => l[left] > target)`, matching the upper-bound example and making the non-`n` exit state explicit;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n`; both excluded ranges are empty, and the point fact is vacuous because `left == right` implies `n == 0`, so `left < n` is false.
- Preservation expectation:
  - after `mid = left + (right - left) / 2`, the active loop condition implies `left <= mid`, `mid < right`, and therefore `0 <= mid < n`; a bridge assertion directly before reading `a[mid]` gives the array-read safety fact and carries the invariant facts.
  - in the `a[mid] <= target` branch, sortedness implies every index up to `mid` has value `<= target`, so assigning `left = mid + 1` extends the lower excluded prefix.
  - in the `else` branch, the failed comparison gives `l[mid] > target`; sortedness extends that to every index from `mid` onward, so assigning `right = mid` extends the upper excluded suffix.
- Exit usefulness: after the loop exits, the invariant plus `!(left < right)` gives `left == right`. If `left > 0` and `a[left - 1] == target`, returning `left - 1` is in range and the suffix fact covers every later index. If the final branch returns `-1`, then either `left == 0` and the suffix covers the whole array with `> target`, or `left > 0` and the failed equality together with the prefix fact and sortedness shows every prefix value is `< target`; the suffix still gives every later value `> target`.

## Planned edit

- Add the upper-bound-style loop invariant before the `while`.
- Add a midpoint bridge assertion after `mid` is computed.
- Add an else-branch bridge assertion recording `l[mid] > target`.
- Add a final-read bridge assertion immediately before `a[left - 1]` is read, carrying `0 <= left - 1 < n` when `left > 0` and the loop-exit partition facts.

## Round 2 - 2026-04-21 04:28:55 +0800

- First `symexec` after adding the invariant and bridge assertions failed with `Fail to Remove Memory Permission of mid:107` at `annotated/verify_20260421_042558_binary_search_last.c:99:8`.
- The failing assertion was the post-loop `Assert` placed between the loop and the final `if`. This matches the known `ASSERTION.md` warning that loop-exit assertions can interfere with local variable cleanup when placed after the loop body in a way that changes local-permission removal.
- The invariant already carries the needed partition facts at loop exit, and the final `if (left > 0 && a[left - 1] == target)` should provide the guard for the final array read.
- Planned edit: remove the post-loop assertion and rerun `symexec`, keeping the loop invariant and in-loop bridge assertions unchanged.
