# Annotation Reasoning

## Initial loop invariant plan

The unannotated working copy reaches `for (i = 1; i < n; ++i)` with no `Inv`, so symbolic execution would have no loop-head state for the two-pointer compaction. The loop-head control point is before the condition check. At that point `i` is the next original-array index to inspect, and `j` is the length of the duplicate-free prefix already written into `a[0..j)`.

The postcondition only constrains the final array to have `remove_duplicates_sorted_spec(l)` as a prefix and allows an existential suffix `t`. Therefore the invariant should avoid over-specifying the overwritten gap between `j` and `i`. I will use an existential current heap list `lc` with `IntArray::full(a, n@pre, lc)`, assert `Zlength(lc) == n@pre`, assert `j == Zlength(remove_duplicates_sorted_spec(sublist(0, i, l)))`, and state that the first `j` elements of `lc` match the duplicate-free spec of the processed original prefix. To keep future reads sound, the invariant also states that every index from `i` through `n - 1` is still equal to the original input list `l`.

The bounds `1 <= i <= n@pre`, `1 <= j <= i`, plus `a == a@pre` and `n == n@pre`, are necessary for array reads `a[i]`, `a[j - 1]`, the possible write `a[j]`, and the return proof. At loop exit, `i == n` together with the prefix property and `j == Zlength(remove_duplicates_sorted_spec(l))` should allow the return witness to choose `lr = lc` and `t = sublist(j, n, lc)`.
