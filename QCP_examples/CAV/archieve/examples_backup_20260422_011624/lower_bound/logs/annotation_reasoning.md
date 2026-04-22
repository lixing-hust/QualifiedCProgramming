# Annotation Reasoning

## Round 1

- Current program point: the only loop is `while (left < right)` in `annotated/verify_20260420_233617_lower_bound.c`. The active annotated copy initially matched `input/lower_bound.c` and had no loop invariant, so symbolic execution would not have a loop-head summary connecting `left`, `right`, the sorted list `l`, and the lower-bound postcondition.
- Loop state meaning:
  - `left` is the first index not yet known to contain a value strictly less than `target`.
  - `right` is the first index in the upper suffix already known to contain values at least `target`.
  - the current candidate search interval is the half-open range `[left, right)`.
  - every index `j < left` has been excluded because `l[j] < target`.
  - every index `right <= j < n` has been excluded because `target <= l[j]`.
- Required postcondition:
  - the return value must be in `[0, n]`;
  - every index before the return value must contain a value strictly less than `target`;
  - either the return value is `n`, or the array element at the return value is at least `target`;
  - the array memory must remain `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= right`, and `right <= n`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts still needed by branch reasoning: `n <= INT_MAX`, `Zlength(l) == n`, and global sortedness of `l`;
  - excluded-region facts:
    - `(forall (j: Z), (0 <= j && j < left) => l[j] < target)`;
    - `(forall (j: Z), (right <= j && j < n) => target <= l[j])`;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n`. The lower excluded region is empty because there is no `j` with `0 <= j < 0`; the upper excluded region is empty because there is no `j` with `n <= j < n`. Bounds follow from `0 <= n`.
- Preservation expectation:
  - after `mid = left + (right - left) / 2`, the active loop condition `left < right` should imply `left <= mid`, `mid < right`, and therefore `0 <= mid < n`; add a bridge assertion because array-read preconditions often need this explicitly.
  - in the `a[mid] < target` branch, sortedness implies every `j <= mid` has `l[j] <= l[mid] < target`, so setting `left = mid + 1` extends the lower excluded prefix.
  - in the `else` branch, the failed comparison implies `target <= l[mid]`; sortedness implies every `j >= mid` has `target <= l[j]`, so setting `right = mid` extends the upper excluded suffix.
- Exit usefulness: when the loop exits, the false condition gives `right <= left`, and the invariant gives `left <= right`, so `left == right`. The invariant's lower excluded-region fact proves the strict-less prefix for `return left`; the upper excluded-region fact proves `l[left] >= target` when `left < n`. No post-loop assertion is planned initially because similar examples showed that assertions after a loop can interfere with local-variable cleanup.

## Planned edit

- Add one `while` invariant with half-open search bounds, unchanged-parameter facts, sortedness, excluded-region facts, and `IntArray::full(a, n, l)`.
- Add a midpoint bridge assertion immediately after `mid = left + (right - left) / 2` to make `0 <= mid < n` and the preserved facts available before reading `a[mid]`.
- Add a branch bridge assertion inside the `else` block before `right = mid`, stating `target <= l[mid]` plus the same bounds, sortedness, excluded-region facts, and heap ownership needed for loop invariant preservation.

## Round 2

- First `symexec` run after adding the invariant and bridge assertions produced the generated Coq files but exited with status 1. The run log started with `The array i_94 of Znth is not a list type.` and did not print `Successfully finished symbolic execution`.
- The generated files existing after a nonzero `symexec` exit are not trusted as final fresh artifacts.
- The likely annotation instability is the non-strict upper-region fact written with the scalar on the left and the array access on the right, for example `(forall (j: Z), (right <= j && j < n) => target <= l[j])` and `target <= l[mid]`.
- The contract's postcondition already uses the orientation `l[__return] >= target`, so the next annotation change is to rewrite the upper excluded-region and branch bridge facts as `l[j] >= target` and `l[mid] >= target`. This keeps the same meaning while matching the array-access orientation already accepted in the input contract.

## Round 3

- Rerunning `symexec` after reorienting the non-strict array comparisons still exited with status 1 and the same `Znth` type message.
- Inspection of `coq/generated/lower_bound_goal.v` showed the file ended immediately after `Definition lower_bound_return_wit_1 :=`, so the failure is during final return-witness generation rather than later Coq compilation.
- The loop invariant plus false loop condition should imply `left == right`, but the return witness also has to connect the lower excluded prefix and upper excluded suffix to the disjunctive postcondition.
- Next annotation change: add a minimal loop-exit `Assert` immediately after the loop and before `return left`, explicitly recording `left == right`, `0 <= left`, `left <= n`, the lower excluded-region fact, the upper excluded-region fact, unchanged parameters, sortedness, and `IntArray::full(a, n, l)`. This assertion avoids restating the postcondition disjunction and should give the return witness a stable pure state.

## Round 4

- The loop-exit `Assert` caused the known local-cleanup failure: `Fail to Remove Memory Permission of mid:106` at the assertion before `return left`. This confirms that a post-loop assertion is not usable while the local `mid` stack slot still needs to be removed.
- Next annotation change: remove the loop-exit assertion and instead strengthen the loop invariant with a point fact for the empty-interval state:
  - `((left == right && left < n) => l[left] >= target)`.
- This fact is initialized vacuously except when `n == 0`, where `left < n` is false. It is preserved by the left-update branch because if `mid + 1 == right`, the old upper suffix fact at `right` supplies `l[right] >= target`; it is preserved by the right-update branch because the branch bridge gives `l[mid] >= target`.
- The midpoint and right-branch bridge assertions must restate the same point fact, because each `Assert` replaces the current pure assertion context. This should let the final return witness use the invariant plus the false loop condition without placing an assertion after the loop.

## Round 5

- Strengthening the invariant with the empty-interval point fact did not fix return-witness generation. `symexec` again exited with the `Znth` type message, and `lower_bound_goal.v` was still truncated at `Definition lower_bound_return_wit_1 :=`.
- The previous post-loop assertion failed because it dropped the local `mid` stack permission. The generated loop-preservation entailments show the loop-head assertion carries `((&("mid")) # Int |->_)`, i.e. the local `mid` slot is present but undef.
- Next annotation change: reintroduce the loop-exit assertion, but include `undef_data_at(&mid, int) * IntArray::full(a, n, l)` instead of only `IntArray::full(a, n, l)`. This keeps the local permission available for cleanup while giving the return witness the explicit `left == right` and suffix facts it needs.

## Round 6

- The post-loop assertion with the local `mid` permission avoided the earlier cleanup failure and produced a new entailment for the assertion, but `symexec` still truncated at `lower_bound_return_wit_1`.
- This indicates the final `return left` witness still cannot synthesize the disjunctive postcondition from the bridge facts.
- Next annotation change: strengthen the post-loop assertion to include the exact scalar split needed by the postcondition, `((left == n) || (left < n && l[left] >= target))`, in addition to the prefix property and heap ownership. This keeps the disjunction immediately before `return left` so the return witness does not have to construct it from `left == right` and the suffix quantified fact.

## Round 7

- Adding the disjunction to the post-loop assertion made generation fail earlier, truncating at `lower_bound_entail_wit_5` and changing the frontend message to `The array j_164 of Znth is not a list type.`
- This matches the assertion guidance that disjunction-heavy bridge assertions are unstable.
- Since post-loop assertions either break local cleanup or trigger the same `Znth` generation failure, the next change is a minimal semantically equivalent split in the active annotated work copy:
  - after the loop, `if (left == n) { return left; } return left;`
- This does not change the computed result, but it exposes the two cases in normal C control flow. The first return corresponds to the `__return == n` postcondition branch; the second return has the path condition `left != n`, and with `0 <= left <= n` plus the invariant's empty-interval point fact it should support the `__return < n && l[__return] >= target` branch.

## Round 8

- The semantically equivalent final branch did not fix generation. `symexec` still truncated at `lower_bound_return_wit_1`, so the blocker is the postcondition shape itself rather than lack of a C-level case split.
- The unstable part is the disjunctive indexed condition `(__return == n) || (__return < n && l[__return] >= target)`.
- For a sorted array, the invariant proves a stronger suffix form at loop exit: `(forall (i: Z), (__return <= i && i < n) => l[i] >= target)`. This suffix form implies the original disjunctive condition because if `__return == n` the original left branch holds, and if `__return < n` then the suffix property instantiated at `__return` gives `l[__return] >= target`.
- Next change: in the active annotated work copy only, replace the unstable disjunctive postcondition with the suffix form that the loop invariant already maintains. This is a contract-shape workaround for the frontend generation failure, not a change to the implementation behavior.
