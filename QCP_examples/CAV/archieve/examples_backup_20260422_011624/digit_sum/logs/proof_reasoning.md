## Manual proof round 1

After the successful `symexec` run, `coq/generated/digit_sum_proof_manual.v` contains three admitted obligations: `proof_of_digit_sum_safety_wit_3`, `proof_of_digit_sum_entail_wit_2`, and `proof_of_digit_sum_entail_wit_3`.

`digit_sum_safety_wit_3` is the overflow check for `sum + n % 10` inside the loop. The available facts include `n > 0`, `0 <= n`, `0 <= sum`, `sum + n <= n_pre`, and `n_pre <= INT_MAX`. The missing arithmetic bridge is `0 <= n % 10 <= n` for positive `n`, after which `sum + n % 10 <= sum + n <= INT_MAX` and the lower bound follows from nonnegativity.

`digit_sum_entail_wit_2` is loop-invariant preservation after `sum += n % 10; n = n / 10`. Besides the same arithmetic bounds, the semantic goal needs `digit_sum_z n = n % 10 + digit_sum_z (n / 10)` under `n > 0`. Since `input/digit_sum.v` defines `digit_sum_z n` through `digit_sum_fuel n (Z.to_nat n)`, I expect this proof to need a small local helper lemma about one unfolding step of `digit_sum_z` for positive `n`.

`digit_sum_entail_wit_3` is the loop-exit assertion. From `n <= 0` and invariant fact `0 <= n`, `n = 0` follows by arithmetic. Rewriting the semantic invariant at `n = 0` should reduce `digit_sum_z 0` to `0`, yielding `sum = digit_sum_z n_pre`.

## Manual proof round 2

The first compile attempts exposed several proof-script issues rather than annotation problems. `digit_sum_fuel_nonpositive` initially used `rewrite Z.leb_le`, but after simplification there was no boolean equality subterm to rewrite; destructing `Z.leb n 0` is more stable. The fuel-stability helper also needed explicit `nat` types and `%nat` inequalities because `Z_scope` made the unannotated `<=` parse as a `Z` relation.

The main semantic helper is now `digit_sum_z_step`, which proves one recursive unfolding step for positive `n`: `digit_sum_z n = n % 10 + digit_sum_z (n ÷ 10)`. It depends on `digit_sum_fuel_stable_ge`, which shows that extra fuel beyond `Z.to_nat n` does not change the computed digit sum. The quotient decrease fact is isolated in `quot_10_lt_pos`.

The generated entailment goals from `entailer!` appeared in reverse order from the contract text for `digit_sum_entail_wit_2`: semantic equality first, then `sum + n % 10 + n ÷ 10 <= n_pre`, then the lower accumulator bound, then quotient upper and lower bounds. Reordering the bullets fixed the mismatch. For integer safety, `rem_10_bounds_pos` gives `0 <= n % 10 <= n`, which directly discharges both bounds for `sum + n % 10`.

Final proof status: `coq/generated/digit_sum_proof_manual.v` compiles, proves all three manual obligations, and contains no `Admitted.` or added `Axiom`.
