# Proof reasoning

## Round 1: replace generated `Admitted.` witnesses with continuation lemmas

After regenerating with `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_202216_longest_increasing_run`, `coq/generated/longest_increasing_run_proof_manual.v` contains six admitted manual witnesses:

```coq
Lemma proof_of_longest_increasing_run_entail_wit_1 : longest_increasing_run_entail_wit_1.
Proof. Admitted.
...
Lemma proof_of_longest_increasing_run_return_wit_2 : longest_increasing_run_return_wit_2.
Proof. Admitted.
```

The relevant generated goals in `longest_increasing_run_goal.v` are:

```coq
longest_increasing_run_entail_wit_1
```

for loop invariant initialization, three loop-preservation cases:

```coq
longest_increasing_run_entail_wit_2_1
longest_increasing_run_entail_wit_2_2
longest_increasing_run_entail_wit_2_3
```

and two return witnesses:

```coq
longest_increasing_run_return_wit_1
longest_increasing_run_return_wit_2
```

The key pure hypothesis in each loop-preservation witness has the form:

```coq
longest_increasing_run_acc cur best (Znth (i - 1) l 0) (sublist i n_pre l) =
  longest_increasing_run_spec l
```

The loop guard gives `i < n_pre`, so `sublist i n_pre l` can be rewritten to:

```coq
Znth i l 0 :: sublist (i + 1) n_pre l
```

After simplification, the Coq recursive step exactly matches the C branches:

- if `Znth (i - 1) l 0 < Znth i l 0`, the next `cur` is `cur + 1`;
- otherwise the next `cur` is `1`;
- the `best` branch chooses the same value as `Z.max best cur'`.

The next edit adds one local helper lemma `sublist_head_cons_Z` and proves each witness with `pre_process`, `entailer!`, explicit `Z.max` simplification by `lia`, and the stored accumulator equation. No axiom is needed.

## Round 2: fix `sublist_self` binder-name mismatch in helper proof

The first compile attempt after replacing `Admitted.` failed before reaching the generated witnesses:

```text
File ".../longest_increasing_run_proof_manual.v", line 49, characters 31-33:
Error: No such bound variable lo (possible names are: l1 and x).
```

The failing line was in `longest_increasing_run_spec_nonempty_acc`:

```coq
rewrite sublist_self with (lo := 0) (hi := Zlength l).
```

This repository's imported `sublist_self` has binders `l1` and `x`, not `lo` and `hi`:

```coq
Lemma sublist_self {A: Type}:
  forall (l1: list A) x,
    x = Zlength l1 ->
    sublist 0 x l1 = l1.
```

Rather than depend on binder names, I will prove the needed tail fact for `sublist 1 n (x :: xs)` directly by unfolding `sublist`, simplifying `skipn 1`, and rewriting `firstn_all` after converting `Zlength xs` to `length xs`.

## Round 3: avoid `destruct ... as ...` under `sac` scope

The next compile attempt failed at the list destruct line:

```text
File ".../longest_increasing_run_proof_manual.v", line 44, characters 16-18:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

The line was:

```coq
destruct l as [| x xs].
```

This matches the known local rule that `Local Open Scope sac` can interfere with list destruct patterns. I will rewrite it into the stable form:

```coq
destruct l.
```

and use the automatically introduced head and tail names in the cons branch.

## Round 4: use existing `sublist_cons2` and `sublist_self` for the nonempty helper

After avoiding the destruct pattern, the direct unfolded proof still failed:

```text
File ".../longest_increasing_run_proof_manual.v", line 53, characters 6-24:
Error: Found no subterm matching "firstn (Datatypes.length ?M3017) ?M3017"
```

The unfolded `sublist` expression was not in the simple `firstn (length xs) xs` shape expected by `firstn_all`. The library already provides the exact structural rewrite needed:

```coq
sublist_cons2 :
  forall m n a (l: list A),
    1 <= m <= n -> n <= Zlength (a::l) ->
    sublist m n (a::l) = sublist (m-1) (n-1) l
```

I will use `sublist_cons2` to reduce `sublist 1 n (z :: l)` to `sublist 0 (n - 1) l`, then use `sublist_self` with the length fact from `Zlength (z :: l) = n`.

## Round 5: rewrite the zero-length return witness before `Zlength_nil_inv`

The next compile reached `proof_of_longest_increasing_run_return_wit_1` and failed:

```text
File ".../longest_increasing_run_proof_manual.v", line 119, characters 8-23:
Error: Unable to apply lemma ... Zlength l = 0 -> l = nil
on hypothesis of type "Zlength l = n_pre".
```

The generated return witness has both `n_pre = 0` and `Zlength l = n_pre`. The proof must first rewrite the length hypothesis with `n_pre = 0`, then apply `Zlength_nil_inv`. I will use a `match goal` block to find those hypotheses by shape instead of relying on brittle generated numbers.

## Round 6: keep the return accumulator equality in the generated orientation

The next compile reached `proof_of_longest_increasing_run_return_wit_2` and failed with:

```text
The term "H7" has type "best = longest_increasing_run_spec l"
while it is expected to have type "longest_increasing_run_spec l = best".
```

After deriving `i = n_pre`, rewriting `sublist n_pre n_pre l` to `nil`, and simplifying the accumulator, the invariant hypothesis already has the exact desired orientation for the generated pure target: `best = longest_increasing_run_spec l`. The previous script applied `symmetry` unnecessarily. I will remove that `symmetry` and use the simplified hypothesis directly.
