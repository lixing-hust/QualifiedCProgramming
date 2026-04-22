# Proof Reasoning

## 2026-04-22 01:13:12 +0800 - Prove loop-exit entailment witness

After strengthening the invariant and rerunning `symexec`, the generated manual proof file contains one obligation:

```coq
Lemma proof_of_array_first_peak_entail_wit_3 :
  array_first_peak_entail_wit_3.
Proof. Admitted.
```

The relevant generated goal is:

```coq
Definition array_first_peak_entail_wit_3 :=
forall (a_pre n_pre: Z) (l: list Z) (i: Z),
  [| i + 1 >= n_pre |] &&
  [| 1 <= i |] &&
  [| i <= n_pre + 1 |] &&
  [| i + 1 <= INT_MAX |] &&
  [| forall j_2,
       0 < j_2 /\ j_2 < i ->
       Znth j_2 l 0 < Znth (j_2 - 1) l 0 \/
       Znth j_2 l 0 < Znth (j_2 + 1) l 0 |] &&
  [| 0 <= n_pre |] &&
  [| n_pre <= INT_MAX |] &&
  [| Zlength l = n_pre |] &&
  IntArray.full a_pre n_pre l
|--
  [| i + 1 >= n_pre |] &&
  [| 1 <= i |] &&
  [| i <= n_pre + 1 |] &&
  [| i + 1 <= INT_MAX |] &&
  [| forall j,
       0 < j /\ j < n_pre - 1 ->
       Znth j l 0 < Znth (j - 1) l 0 \/
       Znth j l 0 < Znth (j + 1) l 0 |] &&
  IntArray.full a_pre n_pre l.
```

This is the loop-exit assertion bridge. The available invariant proves the non-peak property for all `0 < j < i`; the post-exit assertion needs it for all `0 < j < n_pre - 1`. The loop exit fact `i + 1 >= n_pre` gives `n_pre - 1 <= i`, so any `j < n_pre - 1` also satisfies `j < i`. No heap restructuring is needed because the source and target both contain the same `IntArray.full a_pre n_pre l`.

Planned proof:

```coq
unfold array_first_peak_entail_wit_3.
intros.
Intros.
entailer!.
intros j [? ?].
apply H3.
lia.
```

`Intros` should expose the pure assumptions in generated order, where `H3` is the invariant universal. `entailer!` should discharge the unchanged pure facts and heap ownership, leaving only the target universal; `lia` supplies the arithmetic side condition for applying `H3`.
