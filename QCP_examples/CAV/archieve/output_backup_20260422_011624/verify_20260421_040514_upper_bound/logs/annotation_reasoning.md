# Annotation Reasoning

## Round 1

- Current program point: the only loop is `while (left < right)` in `annotated/verify_20260421_040514_upper_bound.c`. The active annotated copy currently has no loop invariant, so symbolic execution has no summary connecting the shrinking binary-search interval, sortedness of `l`, and the upper-bound postcondition.
- Loop state meaning:
  - `left` is the first index not yet known to contain a value `<= target`.
  - `right` is the first index in the upper suffix already known to contain values `> target`.
  - the current candidate interval is the half-open range `[left, right)`.
  - every index `j < left` has already been excluded because `l[j] <= target`.
  - every index `right <= j < n` has already been excluded because `l[j] > target`.
- Required postcondition:
  - the return value is in `[0,n]`;
  - every index before the return value has value `<= target`;
  - either the return value is `n`, or the element at that returned index is `> target`;
  - array ownership remains `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= right`, and `right <= n`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts needed by branch reasoning: `n <= INT_MAX`, `Zlength(l) == n`, and global sortedness of `l`;
  - excluded-region facts:
    - `(forall (j: Z), (0 <= j && j < left) => l[j] <= target)`;
    - `(forall (j: Z), (right <= j && j < n) => l[j] > target)`;
  - a point fact for the empty-interval non-`n` case: `((left == right && left < n) => l[left] > target)`;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n`. The lower excluded prefix and upper excluded suffix are empty, and the empty-interval point fact is vacuous because `left == right` implies `0 == n`, making `left < n` false.
- Preservation expectation:
  - after `mid = left + (right - left) / 2`, the active loop condition should imply `left <= mid`, `mid < right`, and therefore `0 <= mid < n`; add a bridge assertion immediately before reading `a[mid]`.
  - in the `a[mid] <= target` branch, sortedness implies every `j <= mid` has `l[j] <= l[mid] <= target`, so setting `left = mid + 1` extends the lower excluded prefix.
  - in the `else` branch, the failed comparison gives `l[mid] > target`; sortedness implies every `j >= mid` has `l[j] >= l[mid] > target`, so setting `right = mid` extends the upper excluded suffix.
- Exit usefulness: when the loop exits, the false condition and invariant imply `left == right`. The prefix fact proves the universal prefix postcondition. If `left < n`, the invariant point fact proves `l[left] > target`; if `left == n`, the disjunctive postcondition takes its first branch. No post-loop assertion is planned initially because the lower_bound experience showed post-loop assertions can interfere with local variable cleanup.

## Planned edit

- Add one `while` invariant with the half-open bounds, unchanged-parameter facts, sortedness, excluded-region facts, empty-interval point fact, and `IntArray::full(a, n, l)`.
- Add one midpoint bridge assertion immediately after the midpoint assignment.
- Add one else-branch bridge assertion recording `l[mid] > target` before assigning `right = mid`.

## Round 2

- First `symexec` after adding the invariant and bridge assertions reached `End of symbolic execution of function upper_bound` but exited with status 1. `logs/qcp_run.log` reported `The array i_94 of Znth is not a list type. The type is Z`.
- The generated `coq/generated/upper_bound_goal.v` is truncated immediately after `Definition upper_bound_return_wit_1 :=`, while earlier safety and entailment definitions exist. This localizes the blocker to final return-witness generation, not to array-read safety or loop preservation.
- The loop invariant and false loop condition should imply `left == right`; the prefix fact proves `(forall i, 0 <= i && i < left => l[i] <= target)`, and the point fact proves `left < n => l[left] > target`.
- The unstable part is likely the postcondition disjunction `(__return == n) || (__return < n && l[__return] > target)`. Before considering any contract-shape workaround, try a semantically equivalent C-level case split after the loop:
  - `if (left == n) { return left; }`
  - `return left;`
- This keeps the original `Require` / `Ensure` text unchanged while exposing the two return paths separately to the generator. The first path has the left disjunct directly; the second path has `left != n`, and bounds `0 <= left <= n` should give `left < n` for the right disjunct.

## Round 3

- The C-level final branch did not change the blocker. `symexec` again reached the end of `upper_bound` and exited with the same `Znth` type message, with `coq/generated/upper_bound_goal.v` truncated at `Definition upper_bound_return_wit_1 :=`.
- This shows the generator is not merely missing a path split; it is unstable on the indexed disjunctive postcondition itself.
- The loop invariant already maintains the stronger sorted-suffix form `(forall (i: Z), (right <= i && i < n) => l[i] > target)`. At loop exit, `left == right`, so the natural postcondition available from the invariant is `(forall (i: Z), (left <= i && i < n) => l[i] > target)`.
- That suffix form implies the original disjunction: if `left == n`, the original first branch holds; if `left < n`, instantiating the suffix fact at `i = left` gives `l[left] > target`.
- Next change: in the active annotated work copy only, replace the unstable disjunctive indexed return condition with the stronger suffix-form postcondition. This preserves the intended upper_bound semantics and mirrors the successful lower_bound workaround, but it is a frontend contract-shape workaround rather than a pure invariant/assertion edit.
