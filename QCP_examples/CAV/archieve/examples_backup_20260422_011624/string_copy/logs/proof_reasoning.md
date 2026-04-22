# Proof Reasoning

## Round 1

- Read `string_copy_goal.v`, `string_copy_proof_auto.v`, and `string_copy_goal_check.v`.
- Manual obligations generated in `string_copy_proof_manual.v`:
  - `proof_of_string_copy_entail_wit_1`
  - `proof_of_string_copy_entail_wit_2`
  - `proof_of_string_copy_return_wit_1`
- Initial classification:
  - these are witness-construction obligations, not missing memory shape from annotation
  - `entail_wit_1` should be the loop initialization witness
  - `entail_wit_2` should be the loop-preservation witness after copying one character
  - `return_wit_1` should be the final postcondition after writing the terminating `0`
- Expected proof pattern:
  - use `pre_process`
  - choose explicit existential witnesses for the split lists
  - discharge the pure equalities with `rewrite`, `simpl`, and `lia`
  - leave separation-logic framing to `entailer!`

## First proof plan

- For `entail_wit_1`, try witnesses `l1 = nil` and `d1 = d`.
- For `entail_wit_2`, try witnesses:
  - `l1 = app(l1_2, cons(Znth i l 0, nil))`
  - `d1 = tail d1_2`
  - then use the hypothesis `Zlength d1_2 = n + 1 - i` together with `Znth i (l ++ [0]) <> 0` to show `d1_2` is nonempty and the copied character is exactly the next prefix value.
- For `return_wit_1`, use the exit hypothesis `Znth i (l ++ [0]) = 0` and the prefix-equality hypothesis to show that replacing position `i` by `0` yields the complete target list `l ++ [0]`.

## Round 2

- `entail_wit_1` compiled after switching from `intros` to `pre_process`, applying `CharArray.full_length`, and choosing witnesses `d1 = d`, `l1 = nil`.
- `entail_wit_2` needed several proof-state inspections in `coqtop`.
- Stable proof pattern for `entail_wit_2`:
  - derive `Zlength l = n` from `CharArray.full_length src_pre (n + 1) (l ++ [0])`
  - prove `i < n` from the branch assumption `Znth i (l ++ [0]) <> 0`
  - choose witnesses `d1 = tl d1_2`, `l1 = l1_2 ++ [Znth i l 0]`
  - normalize the destination list with `replace_Znth_app_r`, `replace_Znth_nothing`, and explicit `replace (i - i) with 0 by lia`
  - prove the extended prefix property by splitting `k < i + 1` into `k < i \/ k = i`
- Several early failures were just goal-order mistakes after `entailer!`; the remaining pure goals came in this order:
  - destination array shape
  - prefix-equality for `k < i + 1`
  - `Zlength (tl d1_2)`
  - `Zlength (l1_2 ++ [Znth i l 0])`

## Round 3

- After `entail_wit_2` was completed, `proof_of_string_copy_return_wit_1` remained open.
- `coqtop` shows the residual goal after `entailer!` is:
  - `CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)) |-- CharArray.full dst_pre (n + 1) (l ++ [0])`
- Available assumptions at that point are only:
  - `Znth i (l ++ [0]) 0 = 0`
  - `Zlength l1 = i`
  - `Zlength d1 = n + 1 - i`
  - `forall k, 0 <= k < i -> Znth k l1 0 = Znth k l 0`
- This is not enough to identify the suffix `d1` with the suffix of `l ++ [0]`.
- In particular, the contract does not state that `l` contains no internal `0`, so the exit condition `Znth i (l ++ [0]) = 0` does not imply `i = n`.
- Without `i = n` or an equivalent “first zero is the terminator” property, the generated return witness is not derivable from the current contract.

## Round 4

- The previous conclusion was too coarse. Before treating this as a contract gap, I went back to the annotation layer and asked whether the invariant had forgotten a semantic fact from the loop control flow.
- The missing fact was:
  - every already-processed source character is nonzero
- This was added to the invariant as:
  - `forall (k: Z), (0 <= k && k < i) => l[k] != 0`
- After clearing the old generated files and rerunning `symexec`, the new `goal.v` propagated that fact into both `entail_wit_2` and `return_wit_1`.
- This confirmed that the old invariant really was too weak for the proof search; the previous generated VC had forgotten information that the loop semantics actually preserves.

## Round 5

- The regenerated `proof_manual.v` reset all three manual lemmas to `Admitted.`
- I first restored `proof_of_string_copy_entail_wit_1`; it remained the same initialization proof, and the new nonzero-prefix hypothesis was vacuous at `i = 0`.
- `proof_of_string_copy_entail_wit_2` needed one real adjustment:
  - after `entailer!`, the extra nonzero-prefix subgoal appears before the old prefix-equality subgoal
  - the earlier script reused the old bullet order and therefore rewrote the wrong target
- Fix:
  - keep the old destination-shape proof
  - solve the new nonzero-prefix goal first
  - then solve the prefix-equality goal
- After swapping those two pure-goal bullets, `proof_manual.v` compiled again with:
  - `proof_of_string_copy_entail_wit_1` complete
  - `proof_of_string_copy_entail_wit_2` complete

## Round 6

- I then rechecked `proof_of_string_copy_return_wit_1` in `coqtop` under the strengthened invariant.
- The residual goal after `entailer!` is still:
  - `CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)) |-- CharArray.full dst_pre (n + 1) (l ++ [0])`
- The strengthened assumptions now include:
  - `forall k < i, Znth k l 0 <> 0`
- This improves the VC, but it still does not imply:
  - `i = n`
  - or `d1 = [0]`
  - or `l1 = l`
- A concrete counterexample shows the remaining theorem is false under the current contract:
  - choose `n = 1`
  - choose `l = [0]`
  - choose `i = 0`
  - choose `l1 = []`
  - choose `d1 = [42; 99]`
  - then all pure assumptions of `string_copy_return_wit_1` hold:
    - `Znth 0 ([0] ++ [0]) 0 = 0`
    - the `< i` prefix conditions are vacuous
    - `Zlength l1 = 0`
    - `Zlength d1 = 2 = n + 1 - i`
  - but the left-hand destination content is `replace_Znth 0 0 [42; 99] = [0; 99]`
  - and the right-hand postcondition wants `[0; 0]`
- Therefore the remaining blocker is not tactic-level and not invariant-level anymore. The formal statement of `string_copy_return_wit_1` is too weak because the contract allows internal `0` inside `l`.

## Round 7

- Following the retrieval rule, I checked the repository for nearby string examples.
- The closest reusable spec pattern I found is `strlen` in `/home/yangfp/QualifiedCProgramming/QCP_examples/kmp_rel.c`, which also uses `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
- That pattern is enough for length/scanning proofs, but I did not find a completed copy proof that derives full-string reconstruction from this contract alone.
- This matches the counterexample above:
  - the current string predicate is suitable for reading until some `0`
  - it is not strong enough to prove that the first encountered `0` is necessarily the final terminator of `l ++ [0]`

## Round 8

- The earlier “contract gap” diagnosis became stale after the input contract was actually strengthened to exclude internal `0`:
  - `forall (k: Z), (0 <= k && k < n) => l[k] != 0`
- Once the annotated working copy and regenerated VC were aligned with that stronger contract, `return_wit_1` changed shape:
  - the key proof step became showing `i = n` from:
    - `Znth i (l ++ [0]) = 0`
    - `forall k < n, Znth k l 0 <> 0`
    - `i <= n`
- This moved the task back into verify-local proof work; it was no longer blocked at the contract boundary.
- New proof plan for `return_wit_1`:
  - derive `Zlength l = n`
  - derive `i = n` by contradiction on the `i < n` branch
  - prove `l1 = l` by extensionality from the copied-prefix hypothesis and `Zlength l1 = i = n`
  - prove the remaining suffix `d1` has length `1`
  - normalize the final `replace_Znth`

## Round 9

- The remaining work on `return_wit_1` was iterative but purely local.
- The main failure classes and fixes were:
  - side-condition failures:
    - `Cannot find witness` on length goals was fixed by making `Zlength_cons`, `Zlength_nil`, and `Zlength_nonneg` explicit instead of relying on raw `lia`
  - list-normalization failures:
    - `replace_Znth` on the destination tail needed:
      - `replace_Znth_app_r`
      - `replace_Znth_nothing`
      - explicit normalization of the zero index
      - explicit normalization of `Z.to_nat (Zlength l - Zlength l)` to `0%nat`
  - Coq syntax compatibility:
    - `destruct ... as [...]` around the one-element tail repeatedly hit parser issues in this environment
    - switching to more conservative `destruct` forms removed those failures
- Final stable proof shape for `return_wit_1`:
  - derive `i = n`
  - derive `l1 = l`
  - show `d1 = x :: nil` from its length
  - reduce the destination content to `l ++ [0]`
  - finish with `entailer!`
- Final status:
  - `string_copy_proof_manual.v` compiles
  - `string_copy_goal_check.v` compiles
  - the previous “contract gap” conclusion is superseded by the strengthened contract plus regenerated VC
