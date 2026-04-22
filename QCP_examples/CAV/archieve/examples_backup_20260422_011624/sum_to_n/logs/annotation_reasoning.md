## Iteration 1: arithmetic loop summary for `sum_to_n`

The loop guard is checked with `i` equal to the next value that would be added into `ret`.
That means the processed range before each iteration is exactly `1 .. i - 1`.

The postcondition requires the closed form `n * (n + 1) / 2`, so the invariant should keep the accumulator in the same closed form rather than a weaker relational statement.
The natural candidate is:

- `1 <= i && i <= n + 1`
- `n == n@pre`
- `ret == (i - 1) * i / 2`

Initialization:

- before the first guard check, `i == 1` and `ret == 0`
- `(i - 1) * i / 2` becomes `0 * 1 / 2 == 0`
- `1 <= i <= n + 1` follows from the precondition `0 <= n`

Preservation:

- assume the invariant holds at the guard and `i <= n`
- then `ret` summarizes the processed prefix `1 .. i - 1`
- after `ret += i`, the accumulator becomes `i * (i + 1) / 2`
- after `++i`, the next-guard state should satisfy `ret == (i - 1) * i / 2` again

Exit:

- the negated guard gives `i > n`
- together with `i <= n + 1`, we obtain `i == n + 1`
- substituting that into `ret == (i - 1) * i / 2` yields `ret == n * (n + 1) / 2`

This is the smallest invariant that keeps the exact arithmetic summary needed by the postcondition while also preserving the unchanged parameter relation `n == n@pre`.
