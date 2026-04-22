# Proof Reasoning

## Manual proof plan after fresh symexec

- Fresh symbolic execution succeeded and generated `coq/generated/partition_nonnegative_proof_manual.v` with exactly two admitted manual obligations:

```coq
Lemma proof_of_partition_nonnegative_entail_wit_1 : partition_nonnegative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_partition_nonnegative_entail_wit_2_1 : partition_nonnegative_entail_wit_2_1.
Proof. Admitted.
```

- `partition_nonnegative_entail_wit_1` is loop-invariant initialization. The precondition has `0 <= n_pre`, `n_pre <= 2000`, `Zlength l = n_pre`, and `IntArray.full a_pre n_pre l`. The target existential list can be `l`; `Permutation l l` is reflexive, the negative-prefix fact over `p < 0` is vacuous, and the suffix fact over `n_pre - 1 < q < n_pre` is also vacuous by arithmetic.
- `partition_nonnegative_entail_wit_2_1` is loop preservation for the branch where `a[i] >= 0`, after the code has swapped `a[i]` and `a[j]` and decremented `j`. The source heap list is:

```coq
replace_Znth j (Znth i l_cur_2 0)
  (replace_Znth i (Znth j l_cur_2 0) l_cur_2)
```

The target existential should be exactly that swapped list. The remaining proof obligations are pure:

- bounds for `j - 1`, from `i <= j`, `0 <= i`, and `j < n_pre`
- `Permutation l swapped`, from `Permutation l l_cur_2` plus a helper lemma showing the two-index replacement is a swap permutation
- prefix negativity is unchanged because every `p < i` is different from both swapped indices `i` and `j`
- new suffix nonnegativity: for `q = j`, the swapped list contains the old `Znth i l_cur_2 0`, known `>= 0`; for `q > j`, the old suffix invariant applies

- Planned helper shape: define `partition_nonnegative_swap` for the double `replace_Znth`, prove local `replace_Znth` length and `Znth` lemmas, then prove `partition_nonnegative_swap_perm` and direct `Znth` facts for the `i`, `j`, and other positions. This mirrors the completed selection-sort swap proof pattern but is scoped to this generated manual file.

## First compile failure in helper lemma

- Compile command: full `coqc` replay from `/home/yangfp/QualifiedCProgramming/SeparationLogic` through `partition_nonnegative_goal.v`, `partition_nonnegative_proof_auto.v`, `partition_nonnegative_proof_manual.v`, and `partition_nonnegative_goal_check.v`.
- Stable error:

```text
File ".../partition_nonnegative_proof_manual.v", line 54, characters 4-14:
Error: Not an inductive definition.
```

- Failing helper snippet:

```coq
Lemma partition_nonnegative_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros T l.
  induction l; intros.
  - destruct a; destruct b; try lia; reflexivity.
  - destruct a; simpl.
```

- Cause: after `induction l`, Coq used the name `a` for the list head in the cons case, shadowing the numeric index binder named `a`. The tactic `destruct a` was therefore destructing an arbitrary element of type `T`, not a natural number, so Coq correctly reported that the target was not an inductive definition in this context.
- Fix: rename the numeric indices in the helper statement to `m` and `n`, then destruct `m` and `n` in the proof. This matches the selection-sort helper structure and avoids binder shadowing.

## Second compile failure in split-swap length subgoal

- Stable error after the binder-shadowing fix:

```text
File ".../partition_nonnegative_proof_manual.v", line 177, characters 4-7:
Error: Tactic failure:  Cannot find witness.
```

- Failing subgoal was the length half of `list_eq_ext` inside `partition_nonnegative_swap_split_eq`, immediately after rewriting `partition_nonnegative_swap_length`.
- The proof used compact rewriting:

```coq
rewrite !Zlength_app, !Zlength_cons.
lia.
```

- Cause: the compact rewrite did not normalize every nested `Zlength` occurrence enough for `lia` in this proof context. The list shapes are nested as `pref ++ x :: mid ++ y :: tail`, so normalizing one rewrite pattern is fragile.
- Fix: replace the compact line with `repeat rewrite Zlength_app; repeat rewrite Zlength_cons; simpl; lia`, making all length terms explicit before arithmetic.

## Final proof and compile result

- The manual proof now proves both generated obligations without `Admitted.`:
  - `proof_of_partition_nonnegative_entail_wit_1`
  - `proof_of_partition_nonnegative_entail_wit_2_1`
- The main helper package in `partition_nonnegative_proof_manual.v` defines `partition_nonnegative_swap` and proves:
  - double `replace_Znth` preserves length
  - `Znth` at the swapped indices returns the opposite old value
  - `Znth` away from both swapped indices is unchanged
  - the double replacement is a permutation
- The final `proof_of_partition_nonnegative_entail_wit_2_1` uses the generated heap list and unfolds `partition_nonnegative_swap` for the separation-logic heap goal, applies `store_int_undef_store_int` to forget the local `tmp` value, proves the new suffix fact by splitting `q = j` versus `q > j`, proves the prefix unchanged fact using `partition_nonnegative_swap_Znth_other`, and proves permutation by `Permutation_trans` through `partition_nonnegative_swap_perm`.
- Full compile replay succeeded through:

```text
partition_nonnegative_goal.v
partition_nonnegative_proof_auto.v
partition_nonnegative_proof_manual.v
partition_nonnegative_goal_check.v
```

- Final grep of `coq/generated/partition_nonnegative_proof_manual.v` found no `Admitted.` and no top-level `Axiom`.
