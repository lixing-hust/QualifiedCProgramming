## 2026-04-22 01:04:32 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on the current annotated file and generated five manual obligations in `coq/generated/array_longest_nonnegative_run_proof_manual.v`:

```coq
proof_of_array_longest_nonnegative_run_entail_wit_1
proof_of_array_longest_nonnegative_run_entail_wit_2_1
proof_of_array_longest_nonnegative_run_entail_wit_2_2
proof_of_array_longest_nonnegative_run_entail_wit_2_3
proof_of_array_longest_nonnegative_run_return_wit_1
```

The key generated loop-preservation premise is the residual accumulator invariant:

```coq
array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
  array_longest_nonnegative_run_spec l
```

For each loop step, the proof must rewrite the nonempty suffix at index `i` into its head and tail:

```coq
sublist i n_pre l = Znth i l 0 :: sublist (i + 1) n_pre l
```

This requires `0 <= i < n_pre` and `n_pre <= Zlength l`, both present in the generated premise. The closest reusable proof pattern is `examples/longest_increasing_run/coq/generated/longest_increasing_run_proof_manual.v`, which defines the same `sublist_head_cons_Z` helper and then rewrites the accumulator premise in each branch.

The branch-specific obligations are:

- `entail_wit_1`: initialize the invariant. After `entailer!`, unfold `array_longest_nonnegative_run_spec` and rewrite `sublist 0 n_pre l` to `l` using `sublist_self` plus `Zlength l = n_pre`.
- `entail_wit_2_1`: positive/nonnegative element and `current + 1 > best`. Rewrite the suffix, simplify one accumulator step, destruct `Z_le_dec 0 (Znth i l 0)`, discard the impossible branch by `lia`, then replace `Z.max best (current + 1)` with `current + 1`.
- `entail_wit_2_2`: positive/nonnegative element and `current + 1 <= best`. Same suffix rewrite and branch split, but replace `Z.max best (current + 1)` with `best`.
- `entail_wit_2_3`: negative element. Rewrite the suffix, simplify, destruct `Z_le_dec 0 (Znth i l 0)`, discard the impossible branch by `lia`, then replace `Z.max best 0` with `best` using the invariant fact `0 <= best`.
- `return_wit_1`: combine `i >= n_pre` and `i <= n_pre` to get `i = n_pre`, rewrite `sublist n_pre n_pre l` to `nil`, simplify the accumulator premise to `best = spec l`, and let `entailer!` close the heap frame.

Planned edit: add local helper lemma `sublist_head_cons_Z` and replace the five `Admitted.` bodies with conservative scripts that unfold the witness, introduce variables, call `entailer!`, rewrite the accumulator premise, and use `lia` only for pure arithmetic side conditions.
