# Proof Reasoning

## 2026-04-21 23:36: replace generated admitted manual witnesses

After regenerating with logical path `SimpleC.EE.CAV.verify_20260421_232321_array_reverse_in_place`, `coq/generated/array_reverse_in_place_proof_manual.v` contains three admitted manual lemmas:

```coq
Lemma proof_of_array_reverse_in_place_entail_wit_1 : array_reverse_in_place_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_reverse_in_place_entail_wit_2 : array_reverse_in_place_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_reverse_in_place_return_wit_1 : array_reverse_in_place_return_wit_1.
Proof. Admitted.
```

The corresponding goals in `array_reverse_in_place_goal.v` are assertion entailments. `entail_wit_1` is invariant initialization: it must rewrite the invariant list expression at `left = 0`, `right = n_pre - 1` back to the original `l`. `entail_wit_2` is invariant preservation after swapping two endpoints: it must show the double `replace_Znth` list equals the next invariant expression with `left + 1` and `right - 1`. `return_wit_1` is loop exit: under `left >= right`, `left <= right + 1`, and `left = n_pre - 1 - right`, the invariant list expression must equal `rev l`.

First proof attempt will use the shortest standard skeleton from `PROOF.md`: `pre_process; entailer!`, with arithmetic discharged by `lia` if possible. If the list equalities remain, the next step is to inspect the proof state and add local helper lemmas for the three list normalization facts rather than burying large list proofs inside the witness bodies.

## 2026-04-21 23:44 CST - Completed manual proof

The final manual proof uses four local list lemmas:

- `array_reverse_sublist_snoc` rewrites `sublist low high xs` into the
  prefix slice plus the last element, under `low < high`.
- `array_reverse_sublist_extend_right` rewrites the interior slice after
  moving both pointers inward.
- `array_reverse_swap_step` proves the preservation list equality after
  the generated `replace_Znth right ... (replace_Znth left ...)` update.
- `array_reverse_exit_list` proves the return equality by splitting the
  loop exit into `left = right` and `left = right + 1`.

Representative proof iterations:

- A direct `pre_process; entailer!` on the initial invariant witness left
  `IntArray.full a_pre n_pre l |-- IntArray.full a_pre n_pre (l ++ [])`.
  Adding `rewrite app_nil_r` after the `sublist_nil`/`sublist_self`
  simplifications closed the heap entailment.
- The preservation witness reduced to the same list expression modulo the
  arithmetic form `right - 1 + 1`; adding
  `replace (right - 1 + 1) with right by lia` after
  `array_reverse_swap_step` closed it.
- Earlier helper-lemma attempts failed on `sublist_split` side conditions
  after rewriting `Zlength_correct`; the proof now preserves the original
  `Zlength xs = n` fact as `HZlen` and rewrites only the separate length
  hypothesis needed for `firstn`/`skipn`.
- The `replace_Znth` proof needed explicit append-shape normalization,
  explicit `l1`/`l2` arguments for `replace_Znth_app_r`, and
  `replace_Znth_nothing` on the singleton middle slice.
- The exit proof needed explicit arithmetic normalization in the
  `left = right + 1` branch:
  `replace (n - 1 - right) with (right + 1) by lia`, followed by the
  empty-slice rewrite.

`array_reverse_in_place_proof_manual.v` compiles with `coqc`, contains no
`Admitted.`, no `admit`, and no new `Axiom`.
