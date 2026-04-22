## Manual proof plan for `array_sum`

The generated `proof_manual.v` contains four manual obligations:

- `proof_of_array_sum_safety_wit_3`
- `proof_of_array_sum_entail_wit_1`
- `proof_of_array_sum_entail_wit_2`
- `proof_of_array_sum_entail_wit_3`

The two entailment goals match the standard array-sum pattern:

1. The initialization witness should discharge with `entailer!`, because `sum (sublist 0 0 l)` is definitionally `0`.
2. The loop-step witness should rewrite `sublist 0 (i + 1) l` into `sublist 0 i l ++ [Znth i l 0]`, then use `sum_app`.
3. The loop-exit witness should combine `i >= n_pre` and `i <= n_pre` into `i = n_pre`, then rewrite `sublist 0 (Zlength l) l = l`.

The nontrivial goal is `proof_of_array_sum_safety_wit_3`.
Unlike the positive-only `SeparationLogic/examples/sum` proof, this contract allows negative elements, so the prefix sum bound is not immediate from `sum_bound_lt`.
The intended fix is to add a local helper lemma showing:

- if every element of a list is in `[-b, b]`, then the total sum of that list is in `[-Zlength l * b, Zlength l * b]`.

Applied to the prefix `sublist 0 i l` with `b = 10000`, this yields a bound on `ret`.
Combining that with the element bound on `Znth i l 0` gives a bound on `ret + Znth i l 0`.
Since `i < n_pre <= 10000`, the prefix length is at most `10000`, so the arithmetic stays strictly inside 32-bit signed range.

## Iteration notes

- First compile failure: this Coq version rejected the newer `induction ... as [...]` syntax in the local helper lemma; switched to the older induction style used elsewhere in the repo.
- Second compile failure: the signed-prefix helper lemma needed explicit side-condition facts for `Zlength_cons` and `Znth_cons` instead of relying on a compact `lia` proof.
- Third compile failure: `proof_of_array_sum_safety_wit_3` splits into two top-level arithmetic goals after `entailer!`, so the prefix-bound setup had to be proved separately for the lower-bound and upper-bound branches.
- Final compile adjustment: `proof_of_array_sum_entail_wit_3` needed to rewrite through `ret = sum (sublist 0 n_pre l)` and then use `sublist_self` under `f_equal`, instead of rewriting `sublist_full_Zlength` directly.
- After these changes, `array_sum_proof_manual.v` and `array_sum_goal_check.v` both compiled successfully.
