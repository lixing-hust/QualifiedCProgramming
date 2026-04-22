## Manual proof iteration 1

- After a successful `symexec`, `coq/generated/array_count_distinct_sorted_proof_manual.v` contained five admitted obligations:
  - `proof_of_array_count_distinct_sorted_entail_wit_1`
  - `proof_of_array_count_distinct_sorted_entail_wit_2_1`
  - `proof_of_array_count_distinct_sorted_entail_wit_2_2`
  - `proof_of_array_count_distinct_sorted_return_wit_1`
  - `proof_of_array_count_distinct_sorted_return_wit_2`
- The corresponding definitions in `array_count_distinct_sorted_goal.v` show these are pure list/arithmetic obligations plus unchanged `IntArray.full` framing. The key generated invariant clause is:

```coq
count = array_count_distinct_sorted_spec (sublist 0 i_2 l)
```

  and the loop-step obligations need to prove:

```coq
count + 1 =
  array_count_distinct_sorted_spec (sublist 0 (i_2 + 1) l)
```

  in the branch where `Znth i_2 l 0 <> Znth (i_2 - 1) l 0`, and:

```coq
count =
  array_count_distinct_sorted_spec (sublist 0 (i_2 + 1) l)
```

  in the equality branch.
- Existing tactic skeleton: the first attempt should use `pre_process; entailer!` to expose pure assumptions and solve the separation-logic frame. This is not enough by itself because Coq does not know how `array_count_distinct_sorted_spec` changes when extending a prefix by one element.
- Planned helper lemmas:
  - `array_count_distinct_sorted_from_app_one`: unfolds the recursive helper over `xs ++ [x]`.
  - `array_count_distinct_sorted_spec_app_one`: for nonempty `xs`, appending `x` changes the distinct count by `0` or `1` depending on whether `x` equals the previous last element.
  - `last_sublist_prefix`: identifies the last element of `sublist 0 i l` with `Znth (i - 1) l 0`.
  - `array_count_distinct_sorted_spec_sublist_extend`: combines the previous lemmas to rewrite `spec (sublist 0 (i+1) l)` in the two loop branches.
  - `array_count_distinct_sorted_spec_sublist_0_1_one`: proves the loop invariant initialization, using the fact that the post-`n == 0` path has `0 < Zlength l`.
  - `sublist_0_over_length`: normalizes `sublist 0 i l` to `l` at loop exit when `Zlength l <= i`.
- Why this should discharge the obligations: after `pre_process; entailer!`, all remaining goals are arithmetic or one rewrite with the helper lemmas. `entail_wit_2_1` and `entail_wit_2_2` differ only by the branch equality/inequality, so after `array_count_distinct_sorted_spec_sublist_extend`, destructing `Z.eq_dec` and using `lia` should close both. `return_wit_2` only needs `i_2 = n_pre` from `i_2 >= n_pre` and `i_2 <= n_pre`, then `sublist_0_over_length`.

## Manual proof iteration 2

- First compile feedback: `coqc` failed in the unused helper `array_count_distinct_sorted_spec_bounds` with:

```text
Error: Tactic failure: Cannot find witness.
```

  The line was a `lia` call after unfolding `array_count_distinct_sorted_spec` and `Zlength_cons`.
- Diagnosis: this bounds helper was copied as a possible overflow aid, but none of the five generated manual obligations used it. The auto proof file owns the safety witnesses, while this manual file only needs the five entail/return witnesses. Keeping an unused helper with fragile arithmetic only made the manual proof harder to compile.
- Fix: removed `array_count_distinct_sorted_from_bounds` and `array_count_distinct_sorted_spec_bounds` from `proof_manual.v`.

## Manual proof iteration 3

- Second compile feedback: `array_count_distinct_sorted_spec_app_one` failed after unfolding a nonempty list case. Coq had simplified `1 + ...` into low-level `Z` constructor matches, and the final `reflexivity` was too strict for arithmetic reassociation.
- Fix: rewrote the helper to keep the goal in the explicit form:

```coq
1 + array_count_distinct_sorted_from h (tl ++ cons x nil) =
1 + array_count_distinct_sorted_from h tl +
(if Z.eq_dec x (last (h :: tl) d) then 0 else 1)
```

  then used `array_count_distinct_sorted_from_app_one`, an explicit `last` default equality, a case split on `Z.eq_dec`, and `lia`.

## Manual proof iteration 4

- Third compile feedback: Coq rejected `destruct xs as [| h tl]` under the generated file's `Local Open Scope sac` parser context:

```text
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

- Fix: changed that destruct to the older style used by nearby verified examples:

```coq
destruct xs.
```

  and used the generated names `z` and `xs` in the nonempty branch.

## Manual proof iteration 5

- Fourth compile feedback: `proof_of_array_count_distinct_sorted_return_wit_1` failed in the impossible nonempty-list branch after `rewrite Zlength_cons in H2` with another `Cannot find witness` from arithmetic.
- Current hypotheses at that point included `n_pre = 0`, `Zlength (z :: l) = n_pre`, and the branch `l = z :: l_tail`. To make the contradiction explicit, the proof now adds:

```coq
pose proof (Zlength_nonneg l).
lia.
```

- Result: the full compile replay succeeded for `original/array_count_distinct_sorted.v`, `array_count_distinct_sorted_goal.v`, `array_count_distinct_sorted_proof_auto.v`, `array_count_distinct_sorted_proof_manual.v`, and `array_count_distinct_sorted_goal_check.v`. A final grep found no `Admitted.` and no `Axiom` in `array_count_distinct_sorted_proof_manual.v`.
