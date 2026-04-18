## Loop reasoning for `array_sum`

The loop starts with `i = 0` and `ret = 0`, so the processed prefix is empty.
That matches `ret == sum(sublist(0, 0, l))`.

The invariant is checked at the loop guard, so it must describe the state before reading `a[i]`.
At that point:

- `i` is the next array index to read, so the processed portion is `sublist(0, i, l)`.
- `ret` should equal the sum of that processed prefix.
- `0 <= i <= n` keeps the prefix bounds valid.
- `a == a@pre` and `n == n@pre` record that the loop does not modify the input pointer or length.
- `IntArray::full(a, n, l)` preserves the full array ownership and value relation needed for the read and for the postcondition.

For preservation, when `i < n`, the body reads `a[i]` and adds it into `ret`.
That extends the processed prefix from `sublist(0, i, l)` to `sublist(0, i + 1, l)`, so the same invariant shape should hold for the next iteration.

On exit, the negated guard gives `i >= n`, and together with `i <= n` from the invariant we get `i == n`.
Then `sublist(0, n, l)` is the full list because `Zlength(l) == n`, so `ret == sum(l)` matches the function postcondition.
