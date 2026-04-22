# Proof Reasoning

## 2026-04-21 20:15:04 +0800 - Manual witnesses after successful symexec

`symexec` generated `coq/generated/majority_candidate_proof_manual.v` with five admitted manual witnesses:

```coq
Lemma proof_of_majority_candidate_entail_wit_1 : majority_candidate_entail_wit_1.
Proof. Admitted.

Lemma proof_of_majority_candidate_entail_wit_2_1 : majority_candidate_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_majority_candidate_entail_wit_2_2 : majority_candidate_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_majority_candidate_entail_wit_2_3 : majority_candidate_entail_wit_2_3.
Proof. Admitted.

Lemma proof_of_majority_candidate_return_wit_1 : majority_candidate_return_wit_1.
Proof. Admitted.
```

The generated `goal.v` shows that all five obligations are pure list/arithmetic entailments plus unchanged `IntArray.full` ownership. The key generated invariant fact has the shape:

```coq
majority_candidate_acc candidate count (sublist i n_pre l) =
  majority_candidate_spec l
```

The three loop-preservation witnesses differ only by the branch:

```coq
count = 0
Znth i l 0 = candidate /\ count <> 0
Znth i l 0 <> candidate /\ count <> 0
```

Each branch needs the same one-step suffix lemma:

```coq
majority_candidate_acc candidate count (sublist i n l) =
  let '(candidate', count') :=
    majority_candidate_step candidate count (Znth i l 0) in
  majority_candidate_acc candidate' count' (sublist (i + 1) n l)
```

under `0 <= i < n` and `n <= Zlength l`. This follows by rewriting `sublist i n l` to `Znth i l 0 :: sublist (i + 1) n l` and simplifying `majority_candidate_acc`.

The initialization witness also needs a nonempty-spec lemma:

```coq
majority_candidate_acc (Znth 0 l 0) 1 (sublist 1 n l) =
  majority_candidate_spec l
```

under `1 <= n` and `Zlength l = n`. This is just unfolding `majority_candidate_spec` after destructing the nonempty list and normalizing `sublist 1 (Zlength (x :: xs)) (x :: xs)` to `xs`.

The return witness needs the exit bridge `i = n_pre`, derived from `i >= n_pre` and `i <= n_pre`; then `sublist n_pre n_pre l = nil`, so the invariant reduces to `candidate = majority_candidate_spec l`.

Planned edit in `coq/generated/majority_candidate_proof_manual.v`:

1. Add helper lemmas `majority_candidate_sublist_head`, `majority_candidate_spec_nonempty`, and `majority_candidate_acc_sublist_step`.
2. Replace each admitted witness with `unfold ...; pre_process;` followed by the appropriate helper rewrite and `entailer!; unfold coq_prop, andp; simpl; repeat split; try lia; auto`.
3. Compile `goal`, `proof_auto`, `proof_manual`, and `goal_check`; if a witness fails, inspect the exact Coq proof state and append the next iteration here before changing the proof again.

## 2026-04-21 20:15:31 +0800 - First proof compile syntax failure

The first `coqc` attempt failed before any witness proof state:

```text
File ".../majority_candidate_proof_manual.v", line 43, characters 16-18:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).
```

The failing helper line was:

```coq
destruct l as [| x xs].
```

This environment accepts the older style used by existing examples, so I changed the helper to:

```coq
destruct l.
- ...
- rename z into x.
  rename l into xs.
  ...
```

No proof idea changed; this is only syntax compatibility. Next step is to recompile and inspect the first real tactic failure if one appears.

## 2026-04-21 20:15:48 +0800 - `sublist_self` side condition in helper

The next compile failed in the nonempty-spec helper:

```text
File ".../majority_candidate_proof_manual.v", line 55, characters 4-5:
Error: [Focus] Wrong bullet +: Current bullet + is not finished.
```

The unfinished branch was:

```coq
rewrite Zlength_cons.
replace (Z.succ (Zlength xs) - 1) with (Zlength xs) by lia.
rewrite sublist_self.
reflexivity.
```

In this repository, `sublist_self` has the shape `forall l x, x = Zlength l -> sublist 0 x l = l`; rewriting without the explicit equality premise leaves a subgoal open, which caused the next `+` bullet to be rejected. I changed it to:

```coq
rewrite (sublist_self xs (Zlength xs)) by reflexivity.
```

This keeps the same proof but closes the side condition locally.

The following compile then reported:

```text
Found no subterm matching "sublist 0 (Zlength xs) xs" in the current goal.
```

After `sublist_cons2`, the lower bound was still syntactically `1 - 1`, so the target was not yet the exact `sublist 0 (Zlength xs) xs` form. I inserted:

```coq
replace (1 - 1) with 0 by lia.
```

immediately before the `sublist_self` rewrite.

## 2026-04-21 20:16:17 +0800 - Generated variable name mismatch

The next compile reached `proof_of_majority_candidate_entail_wit_2_1` and failed with:

```text
File ".../majority_candidate_proof_manual.v", line 94, characters 10-15:
Error: The variable i_2 was not found in the current environment.
```

I had copied the naming pattern from `array_second_largest`, where `pre_process` renamed the loop index to `i_2`. In this generated proof, the forall-bound loop index remains named `i`. I changed the three loop-preservation proofs and the return proof from `i_2` to `i`; the generated witness definitions confirm that the relevant binder is:

```coq
forall ... (candidate: Z) (count: Z) (i: Z), ...
```

## 2026-04-21 20:16:43 +0800 - Return witness hypothesis number

The next compile reached the return witness and failed with:

```text
The term "H6" has type "1 <= n_pre" while it is expected to have type
"candidate = majority_candidate_spec l".
```

After `pre_process` and `subst i`, the continuation equality is:

```coq
H5 :
  majority_candidate_acc candidate count (sublist n_pre n_pre l) =
  majority_candidate_spec l
```

while `H6` is only the duplicated lower-bound hypothesis. I changed the empty-suffix rewrite from `in H6` to `in H5`, then use `simpl in H5; exact H5`.
