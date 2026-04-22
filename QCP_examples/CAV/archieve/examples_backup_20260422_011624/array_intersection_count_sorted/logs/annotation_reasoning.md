## 2026-04-22 initial loop invariant

Current program point: the only loop is `while (i < n && j < m)` in
`annotated/verify_20260422_005007_array_intersection_count_sorted.c`.  The
current annotated file has no `Inv` before the while loop:

```c
int i = 0;
int j = 0;
int count = 0;
while (i < n && j < m) {
    ...
}
return count;
```

Without an invariant, symbolic execution has no stable description for the
two indices, the accumulator, the preserved array heaps, or the relationship
between the accumulator and `array_intersection_count_sorted_spec(la, lb)`.
The loop state must express that `i` and `j` point at the remaining suffixes,
and that `count` has already accounted for exactly the matches removed from
the front of the original sorted-array problem.

The invariant to add immediately before the loop is:

```c
/*@ Inv
      0 <= i && i <= n &&
      0 <= j && j <= m &&
      0 <= count && count <= i &&
      count <= j &&
      a == a@pre &&
      b == b@pre &&
      n == n@pre &&
      m == m@pre &&
      n <= INT_MAX &&
      m <= INT_MAX &&
      Zlength(la) == n &&
      Zlength(lb) == m &&
      (forall (ai: Z) (aj: Z),
        (0 <= ai && ai <= aj && aj < n) => Znth(ai, la, 0) <= Znth(aj, la, 0)) &&
      (forall (bi: Z) (bj: Z),
        (0 <= bi && bi <= bj && bj < m) => Znth(bi, lb, 0) <= Znth(bj, lb, 0)) &&
      count + array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb)) ==
        array_intersection_count_sorted_spec(la, lb) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, m, lb)
*/
```

Why this should initialize: after `i = 0`, `j = 0`, and `count = 0`, the
remaining suffixes are the whole `la` and `lb`, so the semantic equation
reduces to `0 + spec(la, lb) == spec(la, lb)`.  Bounds and heap facts come
directly from the precondition.

Why this should be preserved: in the equal branch, the Coq spec consumes both
heads and adds one, matching `count++`, `i++`, and `j++`.  In the `a[i] < b[j]`
branch, the spec consumes the current `a` head without changing the count,
matching `i++`.  In the `a[i] > b[j]` branch, the inner recursive scan over
`b` consumes the current `b` head without changing the count, matching `j++`.
The `count <= i` and `count <= j` facts also show `count < INT_MAX` before the
equal branch increment because the loop condition gives `i < n` and
`n <= INT_MAX`.

Why this should be useful at exit: loop exit means `i >= n` or `j >= m`.
Together with the bounds, one suffix is empty, so the remaining spec term is
zero.  The invariant then gives `count == array_intersection_count_sorted_spec(la, lb)`,
which is exactly the return postcondition while the input array heaps are
preserved unchanged.
