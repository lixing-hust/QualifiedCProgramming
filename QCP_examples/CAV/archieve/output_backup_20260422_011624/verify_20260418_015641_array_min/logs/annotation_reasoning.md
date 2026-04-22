## Loop reasoning for `array_min`

The loop starts with `i = 1` and `ret = a[0]`, so the processed prefix is the first element of `l`.
For a nonempty list, `min_list_nonempty(sublist(0, 1, l))` should coincide with `l[0]`, matching the initialization.

The `for` invariant is checked at the loop guard, so it must describe the state before reading `a[i]`.
At that control point:

- `i` is the next index to inspect, so the processed region is `sublist(0, i, l)`.
- `ret` should be the minimum of that processed prefix.
- `1 <= i <= n` keeps the prefix nonempty and within bounds.
- `n == n@pre` and `a == a@pre` make the unchanged parameters explicit, which usually keeps the generated witnesses cleaner.

For preservation, when `i < n`, the body compares `a[i]` with `ret` and stores the smaller one into `ret`.
That matches extending the processed prefix from `sublist(0, i, l)` to `sublist(0, i + 1, l)`.

On exit, `i < n` is false and the invariant already gives `i <= n`, so we can conclude `i == n`.
Then `sublist(0, n, l)` is the whole list because `Zlength(l) == n`, which is exactly the postcondition target.
