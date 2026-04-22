`array_increment` performs an in-place left-to-right update over `a[0..n-1]`.

The loop index `i` denotes the next position to update, so at the loop head:

- `0 <= i <= n`
- the prefix `a[0..i)` has already been incremented by one
- the suffix `a[i..n)` is still equal to the original list `l`

To express that split, the invariant should keep two logical lists:

- `l1` for the processed prefix, with `Zlength(l1) == i` and `forall k < i, l1[k] == l[k] + 1`
- `l2` for the unprocessed suffix, with `Zlength(l2) == n - i`
- `IntArray::full(a, n, l1 ++ l2)` so the concrete array is the concatenation of those two segments
- `forall k` over the suffix to preserve `l2[k] == l[i + k]`

Initialization is immediate with `i = 0`, `l1 = []`, and `l2 = l`.

Preservation after `a[i] = a[i] + 1` moves one element from `l2` into `l1`, keeping the updated relation for the new prefix and the unchanged relation for the remaining suffix.

At loop exit, `i == n` and `Zlength(l2) == 0`, so `l2` is empty and `IntArray::full(a, n, l1)` remains. The prefix property over `l1` is exactly the postcondition witness.
