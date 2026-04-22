# Annotation Reasoning

## 2026-04-21 23:32: initial loop invariant for two-pointer reversal

Current annotated file before this change:

```c
int left = 0;
int right = n - 1;

while (left < right) {
    int tmp = a[left];
    a[left] = a[right];
    a[right] = tmp;
    left++;
    right--;
}
```

The loop has no `Inv`, but the postcondition is `IntArray::full(a, n, rev(l))`. The verifier needs a persistent description of the current array contents at the loop-head control point. At loop entry, `left` is the next left index to swap and `right` is the next right index to swap. The already-processed right suffix of the original list, `sublist(right + 1, n@pre, l)`, has been moved to the front in reverse order. The still-unprocessed middle is exactly `sublist(left, right + 1, l)`. The already-processed left prefix of the original list, `sublist(0, left, l)`, has been moved to the back in reverse order.

The intended loop-head invariant is:

```c
/*@ Inv
      0 <= left && -1 <= right &&
      left <= right + 1 &&
      left == n@pre - 1 - right &&
      n == n@pre && a == a@pre &&
      n@pre == Zlength(l) &&
      IntArray::full(a, n@pre,
        app(rev(sublist(right + 1, n@pre, l)),
            app(sublist(left, right + 1, l),
                rev(sublist(0, left, l)))))
*/
```

Initialization: before the first loop test, `left == 0` and `right == n - 1`. With `0 <= n`, the bounds `0 <= left`, `-1 <= right`, and `left <= right + 1` hold even when `n == 0`. The list expression reduces to `app(rev(sublist(n, n, l)), app(sublist(0, n, l), rev(sublist(0, 0, l))))`, which is the original `l`, matching the precondition heap.

Preservation: each iteration swaps `a[left]` and `a[right]`, then advances `left` and decreases `right`. This moves one element from the unprocessed middle to each processed side. The arithmetic relation `left == n@pre - 1 - right` records that both pointers have moved symmetrically, and `n == n@pre && a == a@pre` keeps the unchanged parameters available for the final witness.

Exit usability: when the loop exits, `left >= right` combines with `left <= right + 1` and the symmetric pointer equation. The middle segment has length zero or one, so the invariant's array expression is exactly `rev(l)` after list normalization. This is the core fact needed for the `Ensure` heap predicate.
