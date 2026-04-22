# Contract Reasoning: two_sum_sorted

## Source

- Raw markdown: `raw/two_sum_sorted.md`
- Target function: `two_sum_sorted`

## Program Semantics

The function scans a nondecreasing integer array with two indices:

- `left` starts at `0`.
- `right` starts at `n - 1`.
- While `left < right`, it computes `a[left] + a[right]`.
- It returns `1` as soon as the sum equals `target`.
- If the sum is smaller than `target`, it increments `left`.
- Otherwise it decrements `right`.
- If the search interval becomes empty, it returns `0`.

The input array is read-only. The implementation does not write through `a`.

## Mathematical Meaning

The return value is Boolean-like:

- return `1` iff there exist indices `i` and `j` such that
  `0 <= i < j < n` and `l[i] + l[j] == target`;
- return `0` iff every pair of distinct ordered indices `i < j` has
  `l[i] + l[j] != target`.

The sortedness precondition is nondecreasing:

```text
forall i j, 0 <= i <= j < n -> l[i] <= l[j]
```

Using the two-index sortedness condition is stronger and more direct than only
adjacent sortedness for the later two-pointer proof obligations.

## Bounds and Memory

Required input constraints:

- `0 <= n`.
- `n <= INT_MAX`.
- `Zlength(l) == n`.
- `IntArray::full(a, n, l)`.
- `l` is nondecreasing.
- For every valid pair `i < j`, `l[i] + l[j]` is within C `int` bounds.

The pair-sum overflow condition is included because the C implementation
computes `s = a[left] + a[right]`. Even though the accessed pairs are selected
by the algorithm, requiring all valid pair sums to be in range is a compact,
stable safety precondition.

For `n == 0`, `right = n - 1` evaluates to `-1` and the loop is skipped. For
`n == 1`, `left == right` and the loop is also skipped. In both cases the
existential pair condition is false and the universal no-pair condition is
vacuously true.

## Coq Dependency Decision

No `input/two_sum_sorted.v` is needed.

The full problem-specific semantics can be expressed directly in the C
contract using quantifiers over the logical list `l`; no extra recursive
function, relation, or bridge predicate is required.

## Contract Shape

The generated C file contains only:

- the standard verification includes,
- the target function,
- its function-level `With`, `Require`, and `Ensure`.

It intentionally contains no verify-stage annotations.
