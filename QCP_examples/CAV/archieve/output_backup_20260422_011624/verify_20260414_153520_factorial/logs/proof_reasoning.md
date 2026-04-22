# Proof Reasoning

## Manual witness inventory

The current generated manual file leaves three lemmas:

- `proof_of_fac_safety_wit_3`
- `proof_of_fac_entail_wit_1`
- `proof_of_fac_entail_wit_3`

All three are pure arithmetic goals. There is no heap-structure proof beyond normal cancellation of `data_at` facts already aligned by the generated VC.

## Witness strategy

### `fac_entail_wit_1`

This is the loop-entry proof. It should reduce to showing:

- `1 <= n_pre + 1` from `0 <= n_pre`
- `1 = factorial 0`

The first part is linear arithmetic. The second part should follow by unfolding `factorial` from `AUXLib.List_lemma`.

### `fac_safety_wit_3`

This is the overflow-safety side condition for `res * i` inside the loop. Under:

- `1 <= i <= n_pre`
- `0 <= n_pre <= 10`
- `res = factorial(i - 1)`

it suffices to show `factorial(i - 1) * i` stays in `int` range. The upper bound should follow by:

- `i - 1 >= 0`
- `i <= 10`
- monotonic small-case reasoning via `factorial_inc` to rewrite
  `factorial(i - 1) * i = factorial((i - 1) + 1) = factorial(i)`
- then prove `factorial(i) <= factorial(10)` and discharge the concrete bound by computation / `vm_compute`.

The lower bound is immediate because the product is nonnegative.

### `fac_entail_wit_3`

This is the post-assignment bridge after `res = res * i`. It reduces to proving:

- `(factorial(i - 1)) * i = factorial(i)` for `1 <= i`

The intended proof is to instantiate `factorial_inc` with `i - 1`, use `1 <= i` to establish `0 <= i - 1`, and rewrite `(i - 1) + 1` to `i`.

## Expected auxiliary facts

The proof should only need:

- `factorial_inc`
- unfolding `factorial` at `0`
- `lia`
- small concrete computation for `factorial 10`

No extra axioms or helper definitions should be necessary.
