# Annotation Reasoning

## Round 1

- Current program point: the only loop is `while (left <= right)` in `annotated/verify_20260420_231624_binary_search.c`. The active annotated copy currently has no invariant, so symbolic execution would have no loop-head summary connecting `left`, `right`, the sorted input list `l`, and the final membership postcondition.
- Loop state meaning:
  - `left` is the first index not yet ruled out by lower-bound comparisons.
  - `right` is the last index not yet ruled out by upper-bound comparisons.
  - indices `j < left` have been excluded because their values are strictly less than `target`.
  - indices `right < j < n` have been excluded because their values are strictly greater than `target`.
- Required postcondition:
  - if a return happens inside the loop, it must return an in-range `mid` with `l[mid] == target`;
  - if the loop exits and returns `-1`, every index `0 <= j < n` must satisfy `l[j] != target`;
  - the array memory must remain `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= n`, `-1 <= right`, `right < n`, and `left <= right + 1`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts that are still needed in branch reasoning: `Zlength(l) == n` and global sortedness of `l`;
  - excluded-region facts:
    - `(forall (j: Z), (0 <= j && j < left) => l[j] < target)`;
    - `(forall (j: Z), (right < j && j < n) => target < l[j])`;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n - 1`. The lower excluded region is empty. The upper excluded region is also empty because `right < j && j < n` becomes `n - 1 < j && j < n`. Bounds follow from `0 <= n`.
- Preservation expectation:
  - when `a[mid] == target`, the function returns immediately, so no next loop-head invariant is needed on that path;
  - when `a[mid] < target`, sortedness implies every `j <= mid` has `l[j] <= l[mid] < target`, so setting `left = mid + 1` extends the lower excluded region;
  - when `a[mid] > target`, sortedness implies every `j >= mid` has `target < l[mid] <= l[j]`, so setting `right = mid - 1` extends the upper excluded region.
- Exit usefulness: when the loop exits, `left > right` and invariant `left <= right + 1` imply `left == right + 1`. Every valid index is then either `< left` or `> right`, so the two excluded-region facts imply the `return -1` postcondition. A small loop-exit assertion should make that exact all-indices non-membership fact explicit before the final return.

## Planned edit

- Add one `while` invariant with the bounds, unchanged-parameter facts, sortedness, excluded-region facts, and `IntArray::full(a, n, l)`.
- Add one loop-exit `Assert` immediately after the loop fixing `left == right + 1` and restating the full-array non-membership fact needed for `return -1`.

## Round 2

- First `symexec` run after adding the invariant reached the loop body but failed at `annotated/verify_20260420_231624_binary_search.c:40:8` with `Cannot derive the precondition of Memory Read`.
- The failing program point is the first read `a[mid]` immediately after `mid = left + (right - left) / 2`.
- The invariant plus loop condition should imply `0 <= left <= mid <= right < n`, but the memory-read checker did not derive this midpoint range automatically.
- Next annotation change: add a bridge `Assert` immediately after the `mid` assignment stating `left <= mid`, `mid <= right`, `0 <= mid`, `mid < n`, unchanged parameters, sortedness, excluded-region facts, and `IntArray::full(a, n, l)`.
- Because the code reads `a[mid]` a second time after the `a[mid] == target` branch falls through, add the same read-precondition bridge immediately before the second read as well. This keeps the fix local to array-read preconditions instead of changing the contract or weakening the loop invariant.

## Round 3

- `symexec` after adding midpoint bridge assertions passed the array-read point but failed near function exit with `Fail to Remove Memory Permission of mid:105` at `annotated/verify_20260420_231624_binary_search.c:84:4`.
- This is the known assertion-placement failure mode: a loop-exit assertion after the loop can interfere with local-variable cleanup, especially when a local variable such as `mid` is still in scope.
- The loop invariant already records the two excluded regions, and the false loop condition gives `right < left`. Together with `left <= right + 1`, proof should be able to derive `left == right + 1` and then show every valid index is excluded.
- Next annotation change: remove the post-loop `Assert` and rely on the invariant plus the loop false condition for the final `return -1` witness. Keep the midpoint bridge assertions because they fixed the memory-read precondition.

## Round 4

- During manual proof, `binary_search_entail_wit_4_1` showed a genuine annotation gap: the generated right-branch preservation VC only had `Znth mid l 0 >= target_pre`.
- That is too weak to prove the strict upper excluded-region invariant after `right = mid - 1`, because the `j == mid` case needs `target_pre < Znth mid l 0`.
- Program point: immediately after `if (a[mid] == target) { return mid; }` and before `if (a[mid] < target)`.
- The control-flow fact from falling through the first `if` is exactly `l[mid] != target`. The second bridge assertion restated bounds and heap ownership but omitted that failed-equality fact, so it was not available in the later else branch.
- Next annotation change: add `(l[mid] != target)` to the second bridge assertion, immediately before the second read of `a[mid]`, then rerun `symexec` and regenerate the Coq VCs.

## Round 5

- After rerunning `symexec`, inspection showed `(l[mid] != target)` had been inserted into the first midpoint bridge before the equality test, not the second bridge after the equality-test fallthrough.
- That first location is too early: before reading `a[mid] == target`, the verifier cannot assume `l[mid] != target`.
- The generated `entail_wit_2` therefore asked for an impossible fact at the first bridge, while `entail_wit_4_1` still lacked the failed-equality fact for the right branch.
- Next annotation change: remove `l[mid] != target` from the first bridge and add it to the second bridge only.

## Round 6

- Even after moving `l[mid] != target` to the second bridge, `coqtop` showed that `pre_process` did not keep the `<>` fact in the proof context for `binary_search_entail_wit_4_1`.
- The right-branch invariant update needs the strict fact `target < l[mid]`, not merely `l[mid] >= target`.
- Program point: inside the `else` branch of `if (a[mid] < target)`, immediately before `right = mid - 1`.
- At that point the path has both failed `a[mid] == target` and failed `a[mid] < target`, so the intended pure fact is `target < l[mid]`.
- Next annotation change: add a local branch assertion in the `else` block that states `target < l[mid]` plus the bounds, sortedness, excluded-region facts, and heap ownership needed for the following assignment.

## Round 7

- The regenerated `binary_search_entail_wit_5_1` still failed because the branch bridge preserved midpoint bounds but did not restate the original loop bounds, in particular `0 <= left`.
- The invariant after `right = mid - 1` needs facts such as `0 <= left`, `left <= n`, `-1 <= right`, `right < n`, and `left <= right + 1`.
- These facts are available from the loop invariant at the read point, but each bridge assertion replaces the current assertion with only the facts it states.
- Next annotation change: add the loop-bound facts to the midpoint bridge before the first read, the bridge after the failed equality test, and the strict right-branch bridge before `right = mid - 1`.
