# Proof Reasoning

## Return witnesses after initial symexec

`symexec` succeeded on `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_032003_string_starts_with.c` and generated `string_starts_with_goal.v`, `string_starts_with_proof_auto.v`, `string_starts_with_proof_manual.v`, and `string_starts_with_goal_check.v`.

The generated manual proof file contains two admitted goals:

- `proof_of_string_starts_with_return_wit_1`
- `proof_of_string_starts_with_return_wit_2`

Both goals are return-postcondition disjunctions. The key precondition is the comparison result over `Znth 0 (app l (0 :: nil)) 0`; the postcondition splits between the nonempty string case (`0 < n`, where the comparison is against `Znth 0 l 0`) and the empty string case (`n = 0`, where the comparison is against the terminating `0`).

The planned proof shape follows the existing `string_is_empty` pattern: run `pre_process`, apply `CharArray.full_length`, derive `Zlength l = n` from the full array length `Zlength (l ++ 0 :: nil) = n + 1`, destruct `l`, and use the empty/nonempty branch to select the correct disjunct. In the empty branch, simplification turns `Znth 0 (nil ++ 0 :: nil) 0` into `0`; in the cons branch, simplification turns both head reads into the same head element.

## First compile failure

The first compile replay got through `string_starts_with_goal.v` and `string_starts_with_proof_auto.v`, then failed in `string_starts_with_proof_manual.v` at line 34 with:

`Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).`

This is not a semantic proof failure; this Coq environment does not accept the `destruct l as [| x xs]` pattern in the current grammar. I will replace it with the older style already used in the example proofs: `destruct l.` followed by branch-local simplification, avoiding explicit constructor-name patterns.

## Second compile failure

After changing to `destruct l.`, compilation again reached `string_starts_with_proof_manual.v` and failed at line 44:

`Error: Not an inductive goal with 2 constructors.`

The failing line was the disjunct selector `right; right; right.`. The generated postcondition uses the separation-logic `||` notation with left association, so the four cases are shaped as `(((case1 || case2) || case3) || case4)`, not as `case1 || (case2 || (case3 || case4))`. The fix is to use selectors for the left-associated tree: case 1 is `left; left; left`, case 2 is `left; left; right`, case 3 is `left; right`, and case 4 is `right`.

## Third compile failure

The next compile failed with `Wrong bullet -: Current bullet - is not finished` immediately after the first branch's `entailer!`. Inspecting the proof state with `coqtop` showed that `entailer!` had reduced the branch to a model-level conjunction:

`([|Zlength nil = 0|] && ([|Znth 0 (0 :: nil) 0 = 0|] && ([|1 = 1|] && CharArray.full ...))) m`

The separation logic frame was already the original `CharArray.full`; the remaining work was pure simplification. I will add the standard generated-proof cleanup `unfold coq_prop, andp; simpl; repeat split; auto; lia` after each `entailer!` in these return witnesses.
