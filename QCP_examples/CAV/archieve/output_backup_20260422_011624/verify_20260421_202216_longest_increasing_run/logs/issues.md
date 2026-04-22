# Issues

## Issue 1: frontend rejected the accumulator helper used by the loop invariant

The first annotated version added a loop invariant at the guard of `for (i = 1; i < n; ++i)`:

```c
longest_increasing_run_acc(cur, best, Znth(i - 1, l, 0), sublist(i, n, l)) ==
  longest_increasing_run_spec(l)
```

This invariant is semantically aligned with the Coq definition in `input/longest_increasing_run.v`, but the first `symexec` run failed before VC generation:

```text
symexec_start: 2026-04-21T20:24:41+08:00
fatal error: Use of undeclared identifier `longest_increasing_run_acc'
in /home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_202216_longest_increasing_run.c:40:4
Symbolic Execution into function longest_increasing_run
symexec_status: 1
```

The cause was that `input/longest_increasing_run.c` declared only:

```c
/*@ Extern Coq (longest_increasing_run_spec : list Z -> Z) */
/*@ Import Coq Require Import longest_increasing_run */
```

Although the imported Coq module defines `longest_increasing_run_acc`, the annotation frontend still requires an `Extern Coq` declaration before that symbol can be used in C annotations. The fix was to add the existing helper's type declaration to the active annotated C:

```c
/*@ Extern Coq (longest_increasing_run_acc : Z -> Z -> Z -> list Z -> Z) */
```

This is not a contract rewrite; it only exposes an already imported Coq helper to the annotation parser. After this edit, the next step is to clear generated Coq files and rerun `symexec`.

## Issue 2: first successful `symexec` used the wrong generated Coq logical prefix

After adding the missing `Extern Coq` declaration, `symexec` succeeded once with:

```bash
--coq-logic-path=SimpleC.EE
```

This generated files whose imports started with:

```coq
From SimpleC.EE Require Import longest_increasing_run_goal.
```

The compile workflow for this workspace requires the generated directory to be compiled under the workspace-specific prefix:

```text
SimpleC.EE.CAV.verify_20260421_202216_longest_increasing_run
```

Using the generic prefix would make the generated files inconsistent with the documented `coqc` template. The fix was to clear:

```text
coq/generated/longest_increasing_run_goal.v
coq/generated/longest_increasing_run_proof_auto.v
coq/generated/longest_increasing_run_proof_manual.v
coq/generated/longest_increasing_run_goal_check.v
```

and rerun `symexec` with:

```bash
--coq-logic-path=SimpleC.EE.CAV.verify_20260421_202216_longest_increasing_run
```

The regenerated `proof_manual.v` and `goal_check.v` then imported:

```coq
From SimpleC.EE.CAV.verify_20260421_202216_longest_increasing_run
  Require Import longest_increasing_run_goal.
```

This aligned the generated files with the compile template.

## Issue 3: manual proof helper initially used unstable `sublist_self` binder names

The first manual proof replaced the generated `Admitted.` witnesses with helper lemmas and witness scripts. The first compile failed in the helper `longest_increasing_run_spec_nonempty_acc`:

```text
File ".../longest_increasing_run_proof_manual.v", line 49, characters 31-33:
Error: No such bound variable lo (possible names are: l1 and x).
```

The failed proof line was:

```coq
rewrite sublist_self with (lo := 0) (hi := Zlength l).
```

The local library version has `sublist_self` binders `l1` and `x`, so the named rewrite was invalid. The proof was changed to avoid binder names and use the existing structural list lemmas:

```coq
rewrite sublist_cons2 by (rewrite ?Zlength_cons in *; lia).
rewrite sublist_self by (rewrite Zlength_cons in Hlen; lia).
reflexivity.
```

This proves that in the nonempty branch, `sublist 1 n (z :: l)` is the tail list when `Zlength (z :: l) = n`.

## Issue 4: `Local Open Scope sac` rejected `destruct l as [| x xs]`

The second compile attempt failed in the same helper with:

```text
File ".../longest_increasing_run_proof_manual.v", line 44, characters 16-18:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

The failing line was:

```coq
destruct l as [| x xs].
```

This is the known interaction where `Local Open Scope sac` can make list destruct intro-patterns parse unstably. The fix was to use the stable form:

```coq
destruct l.
```

and then use the automatically introduced names `z` and `l` in the cons branch.

## Issue 5: zero-length return witness needed length normalization before `Zlength_nil_inv`

The compile later reached `proof_of_longest_increasing_run_return_wit_1` and failed:

```text
Error: Unable to apply lemma ... Zlength l = 0 -> l = nil
on hypothesis of type "Zlength l = n_pre".
```

The generated witness has both:

```coq
Hn : n_pre = 0
Hlen : Zlength l = n_pre
```

The proof must rewrite `Hlen` with `Hn` before applying `Zlength_nil_inv`. The final proof uses a shape-based match to avoid brittle hypothesis numbers:

```coq
match goal with
| Hn : n_pre = 0, Hlen : Zlength l = n_pre |- _ =>
    rewrite Hn in Hlen;
    apply Zlength_nil_inv in Hlen;
    subst l;
    reflexivity
end.
```

After this change the empty-array return witness compiled.

## Issue 6: nonempty return witness had an unnecessary equality symmetry

The last manual proof failure was in `proof_of_longest_increasing_run_return_wit_2`:

```text
The term "H7" has type "best = longest_increasing_run_spec l"
while it is expected to have type "longest_increasing_run_spec l = best".
```

After deriving `i = n_pre`, rewriting `sublist n_pre n_pre l` to `nil`, and simplifying the accumulator equation, the invariant already yields:

```coq
best = longest_increasing_run_spec l
```

The script had inserted `symmetry` before `exact H7`, flipping the goal into the wrong orientation. Removing `symmetry` closed the witness:

```coq
rewrite sublist_nil in H7 by lia.
simpl in H7.
exact H7.
```

After this change, `longest_increasing_run_proof_manual.v` and `longest_increasing_run_goal_check.v` both compiled.

## Final verification result

The final successful compile used the documented order from `/home/yangfp/QualifiedCProgramming/SeparationLogic`:

```bash
coqc ... -Q "$ORIG" "" "$ORIG/longest_increasing_run.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/longest_increasing_run_goal.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/longest_increasing_run_proof_auto.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/longest_increasing_run_proof_manual.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/longest_increasing_run_goal_check.v"
```

All compile logs are empty after the final successful run. `coq/generated/longest_increasing_run_proof_manual.v` contains no `Admitted.` and no new `Axiom`. Non-`.v` files under `coq/` were removed after compilation.
