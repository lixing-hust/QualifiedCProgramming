## Loop reasoning for `is_sorted_nondecreasing`

### Round 1: identify the loop summary

The function scans adjacent pairs from left to right and returns `0` immediately when it finds a descent. If the loop finishes, the postcondition for return value `1` needs a universal statement that every adjacent pair in the whole array is nondecreasing.

The natural summary at loop head is therefore:

- `i` is the next adjacent pair index to check.
- Every pair strictly before `i` has already been checked and satisfies `l[j] <= l[j + 1]`.
- The array contents and scalar parameter `n` are unchanged, so keep `a == a@pre` and `n == n@pre`.
- Preserve `IntArray::full(a, n, l)` through the whole loop.

This yields the candidate invariant:

- `0 <= i <= n`
- `(forall (j: Z), (0 <= j && j + 1 < i) => l[j] <= l[j + 1])`
- unchanged-parameter equalities
- full array ownership

Initialization is immediate at `i = 0` because the quantified premise `j + 1 < 0` is impossible.

Preservation also matches the control flow:

- if `a[i] <= a[i + 1]`, then after `++i` the processed prefix grows by one pair, so the quantified range extends from `< i` to `< i + 1`;
- if `a[i] > a[i + 1]`, the function returns immediately, so this branch should expose the witness pair `i`.

### Round 2: place the minimum assertions

Two assertions are needed at control-point boundaries.

1. Early-return assertion inside the `if` branch.

This assertion fixes:

- `0 <= i && i + 1 < n`, coming from the loop guard;
- `l[i] > l[i + 1]`, matching the existential witness required by the `__return == 0` postcondition;
- unchanged parameters and array ownership.

This should let the generated `return_wit` choose witness `i` directly.

2. Loop-exit assertion right after the `for`.

At loop exit we know `!(i + 1 < n)`, so record `i + 1 >= n`. Combined with the invariant and `0 <= i`, this is enough to strengthen the prefix property from checked pairs `< i` to all pairs `< n`: any `j` with `j + 1 < n` also satisfies `j + 1 <= i`, hence `j + 1 < i` or equivalently `j < i`.

I therefore asserted the final universal property directly after the loop, together with `i + 1 >= n`, unchanged parameters, and full ownership. This keeps the assertion close to the loop exit and avoids pushing exit reasoning down to the final return statement.

### Round 3: fix the missing integer-range fact exposed by proof debugging

The first manual proof attempt revealed that `safety_wit_2` still asked for a proof of `i + 1` being in signed-int range at loop head. Preserving only `0 <= i <= n` was not enough: from `i` being an `int` we get `i <= INT_MAX`, but that still allows `i = INT_MAX`, which does not imply `i + 1 <= INT_MAX`.

This is therefore an annotation-layer gap rather than a Coq-layer gap. The invariant has been strengthened with:

- `i + 1 <= INT_MAX`

and the loop-exit assertion now keeps the same bound. This is the minimum extra fact needed for the tool to justify the loop-condition arithmetic on `i + 1` without redesigning the contract or changing the functional reasoning.

### Round 4: preserve the bound on `n` explicitly

After regenerating the witnesses, the continue-branch proof obligation still needed to establish the next-iteration bound `i + 2 <= INT_MAX`. The branch assumptions only expose:

- `i + 1 < n`
- the current invariant facts

so the proof can only derive `i + 2 <= INT_MAX` if the invariant also carries an explicit upper bound on `n`.

I therefore added:

- `n <= INT_MAX`

to the invariant and the loop-exit assertion. Together with `i + 1 < n`, this gives the next-head range fact by pure arithmetic, while remaining consistent with the C type of `n` and the fixed contract.
