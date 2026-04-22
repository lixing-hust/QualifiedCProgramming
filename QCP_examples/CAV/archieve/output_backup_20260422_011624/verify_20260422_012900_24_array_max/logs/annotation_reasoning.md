## Loop reasoning for `array_max`

The loop starts at `i = 1` with `ret = a[0]`, so the processed prefix is the first element of `l`.
For a nonempty list, `max_list_nonempty(sublist(0, 1, l))` should match `l[0]`, which aligns with the initialization.

The loop control point is the `for` condition, so the invariant should describe the state before reading `a[i]`.
At that point:

- `i` is the next index to inspect, so the processed region is `sublist(0, i, l)`.
- `ret` should equal the maximum of that processed prefix.
- `1 <= i <= n` is needed because the prefix is always nonempty.
- `n == n@pre` and `a == a@pre` preserve the unchanged parameters explicitly.

On preservation, when `i < n`, the body compares `a[i]` with `ret` and updates `ret` to the larger one.
That matches extending the processed prefix from `sublist(0, i, l)` to `sublist(0, i + 1, l)`.

On exit, `i < n` is false and the invariant gives `i <= n`, so we obtain `i == n`.
Then the processed prefix is the full list `sublist(0, n, l)`, which should reduce to `l` because `Zlength(l) == n`.
