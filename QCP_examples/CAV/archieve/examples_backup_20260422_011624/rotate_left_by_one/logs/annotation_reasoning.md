# Annotation reasoning

## 2026-04-19 initial loop invariant

- Program point: the `for (i = 0; i + 1 < n; ++i)` loop in `rotate_left_by_one`.
- Current annotated file has no loop invariant, so `symexec` would not have a stable assertion at the loop head.
- Loop-state interpretation:
  - At loop-head index `i`, elements at indices `0 <= k < i` have already been shifted left, so they should equal the original `l[k + 1]`.
  - Elements from `i` through `n - 1` have not yet been overwritten, so they remain the original suffix `sublist(i, n, l)`.
  - The saved scalar `first` must remain equal to the original `l[0]`, because it is written to `a[n - 1]` after the loop.
- Planned invariant:
  - Keep bounds `0 <= i && i <= n@pre - 1`, parameter equalities `n == n@pre` and `a == a@pre`, original length `Zlength(l) == n@pre`, and scalar fact `first == l[0]`.
  - Represent the current array contents as `app(l1, sublist(i, n@pre, l))`, where `Zlength(l1) == i` and each prefix element satisfies `l1[k] == l[k + 1]`.
- Initialization: at `i = 0`, choose `l1 = nil`; `app(nil, sublist(0, n, l))` is the original array.
- Preservation: when `i + 1 < n`, the read `a[i + 1]` comes from the still-original suffix and equals `l[i + 1]`; writing it to `a[i]` extends the shifted prefix by one element and leaves the remaining suffix from `i + 1`.
- Exit use: with invariant bounds and `!(i + 1 < n)`, exit gives `i == n - 1`, so the array is the shifted prefix plus the original last element. The following assignment `a[n - 1] = first` completes the rotation postcondition.
