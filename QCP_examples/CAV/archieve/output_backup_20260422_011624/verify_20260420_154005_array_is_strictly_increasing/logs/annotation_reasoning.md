## Loop reasoning for `array_is_strictly_increasing`

### Round 1: initial invariant and assertions

Timestamp: 2026-04-20 15:41:23 +0800

The loop scans adjacent pairs from left to right. At loop head, `i` is the next right-hand index to check, so the already-processed pairs are exactly those whose right-hand index `j` satisfies `1 <= j && j < i`. The successful return path needs the postcondition `(forall (j: Z), (1 <= j && j < n) => l[j - 1] < l[j])`, so the loop invariant should preserve this property over the processed prefix.

The invariant cannot use `i <= n` because the loop initializes `i = 1` even when `n = 0`; requiring `i <= n` would fail before the first loop guard check. Instead, the candidate bound is `1 <= i && i <= n + 1`, which initializes for all `0 <= n` and is preserved by `++i` when the loop guard gives `i < n`. The invariant also keeps `a == a@pre`, `n == n@pre`, and `IntArray::full(a, n, l)` because the function does not write memory and the postcondition must return the same full array ownership.

Inside the early-return branch, the guard and failed comparison expose the witness `i` directly: `1 <= i && i < n && l[i - 1] >= l[i]`. I will add an `Assert` immediately before `return 0` with those facts plus unchanged parameters and array ownership.

After the loop, the negated guard gives `i >= n`. Together with the invariant over all processed right-hand indices `< i`, this implies the postcondition's universal property over all indices `< n`; I will add a minimal loop-exit `Assert` before `return 1` recording `i >= n` and the full-array postcondition property.
