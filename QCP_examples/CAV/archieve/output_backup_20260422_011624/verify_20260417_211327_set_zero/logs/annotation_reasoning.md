# Annotation Reasoning

## Semantic understanding

`set_zero` walks the array from index `0` to `n - 1` and overwrites each cell with `0`. The contract is already fixed: we start with ownership of `IntArray::full(a, n, l)` and must return ownership of the same array with abstract contents `zeros(n)`.

## Invariant choice

The loop variable `i` is the next cell to overwrite. At the loop test, the processed prefix is `[0, i)` and the untouched suffix is `[i, n)`. The invariant therefore keeps:

- `0 <= i <= n@pre`
- `a == a@pre`
- `n@pre == Zlength(l)`
- `IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))`

This preserves exactly the semantic split we need: the prefix has already been zeroed, and the suffix still matches the original logical list `l`.

## Bridge assertions

Before the store, the verifier needs direct write permission for `a[i]`, so the full-array predicate should be opened into:

- `IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l)))`
- `data_at(a + (i * sizeof(int)), int, l[i])`

After writing `0`, the cell can be folded back into:

- `IntArray::full(a, n@pre, app(zeros(i + 1), sublist(i + 1, n@pre, l)))`

## Loop exit

On exit, the loop guard gives `i >= n`, and together with the invariant bound `i <= n@pre` this should collapse to `i = n@pre`. Substituting that into the invariant leaves the whole array equal to `zeros(n@pre)`, so no extra exit assertion should be necessary.

## Risk check

- Bounds are standard loop-index obligations from `0 <= i < n@pre`.
- The only mutation is `a[i]`.
- The parameter-equality facts are kept explicitly to avoid witness pollution.
- I am intentionally not adding a post-loop assertion because the existing experience notes show that a late exit assertion can interfere with local-permission cleanup.
