## 2026-04-22 manual proof start after successful symexec

Fresh `symexec` succeeded for the current annotated file and generated
`coq/generated/array_intersection_count_sorted_goal.v`,
`array_intersection_count_sorted_proof_auto.v`,
`array_intersection_count_sorted_proof_manual.v`, and
`array_intersection_count_sorted_goal_check.v`.  The generated manual file has
six admitted obligations:

```coq
proof_of_array_intersection_count_sorted_entail_wit_1
proof_of_array_intersection_count_sorted_entail_wit_2_1
proof_of_array_intersection_count_sorted_entail_wit_2_2
proof_of_array_intersection_count_sorted_entail_wit_2_3
proof_of_array_intersection_count_sorted_return_wit_1
proof_of_array_intersection_count_sorted_return_wit_2
```

The key generated preservation goals are:

```coq
count + array_intersection_count_sorted_spec
          (sublist i n la) (sublist j m lb)
= array_intersection_count_sorted_spec la lb
```

must imply the same equation after advancing only `j` in the `a[i] > b[j]`
branch, after advancing only `i` in the `a[i] < b[j]` branch, and after
advancing both plus incrementing `count` in the equality branch.  These are
pure list/spec facts once the heap frame is handled by `entailer!`.

The current proof script is only:

```coq
Lemma proof_of_array_intersection_count_sorted_entail_wit_2_3 :
  array_intersection_count_sorted_entail_wit_2_3.
Proof. Admitted.
```

This is insufficient because `entailer!` does not know how to unfold the
recursive spec over `sublist i n` and `sublist j m`.  I will add local helper
lemmas in `proof_manual.v`:

- `array_intersection_count_sorted_sublist_head`, rewriting a nonempty suffix
  `sublist i n l` to `Znth i l 0 :: sublist (i+1) n l`.
- branch recurrence lemmas for equal, less-than, and greater-than heads.
- nil-suffix lemmas for return witnesses when either loop index has reached
  its bound.

The witness proofs should then use `pre_process`, rewrite the appropriate
helper lemma, and finish pure arithmetic with `lia`, leaving spatial
ownership to `entailer!`.

## 2026-04-22 first compile failure in helper syntax

The first compile replay used the documented load path from
`/home/yangfp/QualifiedCProgramming/SeparationLogic` and compiled the original
spec, generated goal, and generated auto proof before stopping in the manual
proof file:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 38, characters 17-19:
Error:
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).
```

The failing snippet was:

```coq
Lemma array_intersection_count_sorted_spec_nil_r :
  forall a, array_intersection_count_sorted_spec a nil = 0.
Proof.
  induction a as [| x xs IH]; simpl; auto.
Qed.
```

This is not a semantic proof issue.  The local Coq/parser configuration is
rejecting that induction intro-pattern form.  I will rewrite it to a simpler
`intros a; induction a; simpl; auto.` form and rerun the same compile command.

## 2026-04-22 second compile failure in compact destruct syntax

After simplifying the induction, compile reached the less-than branch helper
and stopped at:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 73, characters 55-57:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

The failing compact tactic was:

```coq
destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)); [lia|].
```

This is again a proof-script syntax issue rather than a missing fact.  I will
replace compact bracketed alternatives in the branch helpers with explicit
bullets, keeping the same case split and arithmetic reasoning.

## 2026-04-22 return witness hypothesis numbering

After the branch helper syntax repair, compile reached
`proof_of_array_intersection_count_sorted_return_wit_1` and failed with:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 134, characters 2-35:
Error: Found no subterm matching "sublist ?M8825 ?M8826 ?M8824" in H13.
```

The guessed hypothesis `H13` was the sortedness fact for `lb`, not the semantic
loop invariant.  A `coqtop` probe after `pre_process` showed the relevant fact
is:

```coq
H14 :
  count +
  array_intersection_count_sorted_spec (sublist i_3 n_pre la)
    (sublist j_3 m_pre lb) = array_intersection_count_sorted_spec la lb
```

I will replace numbered rewrites with a `match goal` that selects the semantic
equation by shape.  For `return_wit_1`, `j_3 >= m_pre` and `j_3 <= m_pre` make
`sublist j_3 m_pre lb = nil`, then `array_intersection_count_sorted_spec_nil_r`
turns the remaining spec into `0`.  For `return_wit_2`, `i_3 >= n_pre` and
`i_3 <= n_pre` make `sublist i_3 n_pre la = nil`, and simplification turns the
remaining spec into `0`.

## 2026-04-22 proof completion

The return proof was repaired by matching the semantic equation by context:

```coq
match goal with
| Hspec: context [array_intersection_count_sorted_spec _ (sublist ?j ?m lb)] |- _ =>
    rewrite (sublist_nil lb j m) in Hspec by lia;
    rewrite array_intersection_count_sorted_spec_nil_r in Hspec;
    assert (count = array_intersection_count_sorted_spec la lb) by lia
end.
```

and the symmetric first-argument version for `return_wit_2`.  This avoids
depending on generated hypothesis numbers such as `H14`.

The full compile replay then succeeded for:

```text
original/array_intersection_count_sorted.v
coq/generated/array_intersection_count_sorted_goal.v
coq/generated/array_intersection_count_sorted_proof_auto.v
coq/generated/array_intersection_count_sorted_proof_manual.v
coq/generated/array_intersection_count_sorted_goal_check.v
```

`proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.  The final
`goal_check.v` compile passed under logical prefix
`SimpleC.EE.CAV.verify_20260422_005007_array_intersection_count_sorted`.
