# Annotation Reasoning

## Round 1

- Current program point: the only loop is `while (left < right)` in `annotated/verify_20260421_143138_two_sum_sorted.c`. The active annotated copy currently has no invariant, so symbolic execution has no loop-head summary connecting the two pointer window to the existential/nonexistential two-sum postcondition.
- Loop state meaning:
  - `left` is the smallest index still inside the candidate window.
  - `right` is the largest index still inside the candidate window.
  - Pairs with first index `i < left` have already been ruled out.
  - Pairs with second index `j > right` have already been ruled out.
- Required postcondition:
  - if the loop finds `a[left] + a[right] == target`, the return value `1` must be justified by witnesses `left` and `right`, with `0 <= left < right < n`;
  - if the loop exits and returns `0`, every pair `0 <= i < j < n` must have sum different from `target`;
  - the input array must remain `IntArray::full(a, n, l)`.
- Planned invariant:
  - numeric bounds: `0 <= left`, `left <= n`, `-1 <= right`, `right < n`, and `left <= right + 1`;
  - unchanged parameters: `a == a@pre`, `n == n@pre`, and `target == target@pre`;
  - contract facts still needed in branch reasoning: `n <= INT_MAX`, `Zlength(l) == n`, sortedness of `l`, and the pair-sum overflow guard;
  - excluded-pair facts split into two implications:
    - `(forall (i: Z) (j: Z), (0 <= i && i < j && j < n && i < left) => l[i] + l[j] != target)`;
    - `(forall (i: Z) (j: Z), (0 <= i && i < j && j < n && right < j) => l[i] + l[j] != target)`;
  - unchanged heap ownership: `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `left == 0` and `right == n - 1`. The lower excluded-pair fact is vacuous because no valid `i` satisfies `i < 0`. The upper excluded-pair fact is vacuous because no valid `j < n` satisfies `n - 1 < j`. Bounds follow from `0 <= n`.
- Preservation expectation:
  - if `s == target`, the function returns immediately with witnesses `left` and `right`;
  - if `s < target`, sortedness implies every pair using the old `left` and any `j <= right` has sum at most `l[left] + l[right] < target`, while pairs with `j > right` were already excluded, so `left++` preserves the lower excluded fact;
  - if `target < s`, sortedness implies every pair using the old `right` and any `i >= left` has sum at least `l[left] + l[right] > target`, while pairs with `i < left` were already excluded, so `right--` preserves the upper excluded fact.
- Exit usefulness: when the loop exits, `left >= right` and invariant `left <= right + 1` imply every valid pair has either `i < left` or `right < j`, so the two excluded-pair facts cover the universal no-solution postcondition.

## Planned edit

- Add one `while` invariant with the bounds, unchanged-parameter facts, sortedness, pair-sum range guard, split excluded-pair facts, and `IntArray::full(a, n, l)`.
- Add a top-of-loop bridge assertion before reading `a[left]` and `a[right]` so the memory read and pair-sum range facts are explicit.
- Add branch-local assertions before `left++` and `right--` to keep the strict `l[left] + l[right] < target` or `target < l[left] + l[right]` fact available for invariant preservation after pointer movement.

## Round 2

- First `symexec` run after adding the initial invariant and bridge assertions failed at `annotated/verify_20260421_143138_two_sum_sorted.c:77:8` with `cannot find the program variable s(111) in assertion, please check the @pre or related which implies`.
- The failing program point is the pre-assignment `Assert` immediately before `s = a[left] + a[right]`.
- Diagnosis: `s` is a local variable that has been declared but not assigned yet. The bridge assertion before the assignment restated heap and pure facts but did not mention the local variable `s`; this drops or mismatches the local-variable permission before the assignment.
- Next annotation change: remove the pre-assignment bridge assertion and instead add a bridge immediately after `s = a[left] + a[right]`, where it can explicitly state `s == l[left] + l[right]`. Also add `s == l[left] + l[right]` to the branch-local assertions so the later branch facts derived from `s < target` and `s != target` remain connected to the list expression.
