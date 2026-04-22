# Proof Reasoning

## Initial manual proof pass

Fresh symbolic execution generated five manual obligations in `coq/generated/remove_duplicates_sorted_proof_manual.v`: `proof_of_remove_duplicates_sorted_entail_wit_1`, `proof_of_remove_duplicates_sorted_entail_wit_2_1`, `proof_of_remove_duplicates_sorted_entail_wit_2_2`, `proof_of_remove_duplicates_sorted_return_wit_1`, and `proof_of_remove_duplicates_sorted_return_wit_2`.

The first obligation initializes the loop invariant after `j = 1` for the nonempty input case. The middle two obligations preserve the loop invariant for the unequal branch that writes `a[j] = a[i]` and increments `j`, and for the equal branch that only advances `i`. The two return witnesses handle `n == 0` and loop exit with `i == n`.

The generated contexts contain a current heap list `lc`, pointwise prefix and suffix facts, and the custom Coq function `remove_duplicates_sorted_spec`. The first attempt will replace the generated `Admitted.` placeholders with the minimal skeleton `pre_process; entailer!` and then compile to identify which subgoals require custom list lemmas about `sublist`, `Znth`, `replace_Znth`, and the duplicate-removal spec.

## Manual proof repair

The skeleton compiled only because the generated placeholders still ended in `Admitted.`. After changing the first and empty-return witnesses to `Qed`, Coq exposed the real list obligations. The invariant initialization needed the fact that `sublist 0 1 l` is the singleton `[Znth 0 l 0]`, which is obtained from `sublist_single` after explicitly changing `1` to `0 + 1`.

For loop preservation, the hard facts were the two recurrence cases for `remove_duplicates_sorted_spec (sublist 0 (i + 1) l)`. I added local helpers `rds_last`, `rds_from_snoc`, `rds_from_last_cons`, and `rds_spec_snoc`. These prove that appending the next original element either extends the duplicate-free spec by one element or leaves it unchanged, depending on comparison with the last kept element. The branch guard is over the current heap list `lc`, so the proof first rewrites `a[i]` back to `l[i]` with the suffix invariant and rewrites `a[j-1]` back to the last element of the spec with the prefix invariant.

The unequal branch uses `replace_Znth` as the witness heap list. Local lemmas `replace_Znth_length`, `Znth_replace_Znth_eq`, and `Znth_replace_Znth_other` discharge the length, updated index, and untouched-index cases. The equal branch keeps `lc` unchanged and uses the equality branch of `rds_spec_snoc`.

For the nonempty return witness, the loop exit facts give `i = n`. I proved `sublist 0 n l = l`, chose `lr = lc` and `t = sublist j n lc`, and used `list_eq_by_Znth` to prove `lc = remove_duplicates_sorted_spec l ++ sublist j n lc`. The prefix part comes from the invariant; the suffix part follows from `Znth_sublist`.

The final manual proof compiles with no `Admitted.` and no local `Axiom` declaration.
