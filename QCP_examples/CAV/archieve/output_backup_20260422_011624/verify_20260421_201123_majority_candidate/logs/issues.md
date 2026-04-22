# Verification Issues

## Loop invariant needed continuation semantics

- Symptom: The original annotated file had no `Inv` before `for (i = 1; i < n; ++i)`, so `symexec` had no way to connect the final `candidate` to `majority_candidate_spec(l)`.
- Trigger: `majority_candidate` updates two local state variables, `candidate` and `count`, while the postcondition only mentions the final candidate. A weak invariant such as array preservation and bounds would not preserve the fold semantics needed by the return witness.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_201123_majority_candidate.c`, immediately before the loop.
- Fix: Added an invariant that records the continuation property:

```c
majority_candidate_acc(candidate, count, sublist(i, n@pre, l)) ==
  majority_candidate_spec(l)
```

plus loop bounds, `0 <= count && count <= i`, parameter equalities, and unchanged `IntArray::full(a, n@pre, l)`.
- Result: `symexec` succeeded and generated `majority_candidate_goal.v`, `majority_candidate_proof_auto.v`, `majority_candidate_proof_manual.v`, and `majority_candidate_goal_check.v`.

## Manual proof helpers needed for suffix-step normalization

- Symptom: `coq/generated/majority_candidate_proof_manual.v` initially contained five admitted lemmas:

```coq
proof_of_majority_candidate_entail_wit_1
proof_of_majority_candidate_entail_wit_2_1
proof_of_majority_candidate_entail_wit_2_2
proof_of_majority_candidate_entail_wit_2_3
proof_of_majority_candidate_return_wit_1
```

- Trigger: The generated VCs were pure list/arithmetic obligations about `majority_candidate_acc` over `sublist i n l`, and automation did not unfold the suffix by one array element.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_201123_majority_candidate/coq/generated/majority_candidate_proof_manual.v`.
- Fix: Added local helper lemmas:

```coq
majority_candidate_sublist_head
majority_candidate_spec_nonempty
majority_candidate_acc_sublist_step
```

The branch witnesses call `majority_candidate_acc_sublist_step`, unfold `majority_candidate_step`, split on `Z.eq_dec`, and finish arithmetic/memory obligations with `entailer!` and `lia`. The return witness derives `i = n_pre`, rewrites `sublist n_pre n_pre l` to `nil`, and simplifies the accumulator.
- Result: All manual proof lemmas compile, and `proof_manual.v` contains no `Admitted.` and no new `Axiom`.

## Coq syntax and helper-lemma compatibility adjustments

- Symptom: The first proof compile failed with:

```text
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

on:

```coq
destruct l as [| x xs].
```

- Fix: Rewrote the helper proof using the older style accepted by this environment:

```coq
destruct l.
- ...
- rename z into x.
  rename l into xs.
```

- Symptom: The next compile failed with a bullet error because `rewrite sublist_self` left its explicit length premise open. A follow-up attempt also showed the lower bound was syntactically `1 - 1` rather than `0`.
- Fix: Normalized the bounds before rewriting:

```coq
replace (1 - 1) with 0 by lia.
replace (Z.succ (Zlength xs) - 1) with (Zlength xs) by lia.
rewrite (sublist_self xs (Zlength xs)) by reflexivity.
```

- Symptom: A later compile failed because the proof used `i_2`, copied from a different example, but this generated proof kept the loop index as `i`.
- Fix: Updated the loop-preservation and return proofs to refer to `i`.
- Symptom: The return proof initially rewrote the wrong hypothesis number:

```text
The term "H6" has type "1 <= n_pre" while it is expected to have type
"candidate = majority_candidate_spec l".
```

- Fix: Rewrote the actual continuation equality `H5`:

```coq
replace (sublist n_pre n_pre l) with (@nil Z) in H5.
```

- Result: The full compile template passed through `majority_candidate_goal_check.v`.
