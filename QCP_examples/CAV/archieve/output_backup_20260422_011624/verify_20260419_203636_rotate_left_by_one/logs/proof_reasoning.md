# Proof reasoning

## 2026-04-19 manual proof start

- `symexec` succeeded and generated `rotate_left_by_one_goal.v`, `rotate_left_by_one_proof_auto.v`, `rotate_left_by_one_proof_manual.v`, and `rotate_left_by_one_goal_check.v`.
- `rotate_left_by_one_proof_manual.v` contains three admitted obligations:
  - `proof_of_rotate_left_by_one_entail_wit_1`: initialize the loop invariant before the first loop test.
  - `proof_of_rotate_left_by_one_entail_wit_2`: prove the invariant is preserved after one shift assignment.
  - `proof_of_rotate_left_by_one_return_wit_1`: prove the final postcondition after writing `first` to `a[n - 1]`.
- The generated files compile with the placeholders, so the current blocker is proof content rather than load path or VC generation.
- Current proof plan:
  - For `entail_wit_1`, instantiate the invariant prefix with `nil` and normalize `sublist 0 n l` to `l`.
  - For `entail_wit_2`, add a helper lemma showing that writing `a[i] = a[i+1]` transforms `app l1 (sublist i n l)` into `app (l1 ++ [l[i+1]]) (sublist (i+1) n l)`, then instantiate the next prefix with that appended list.
  - For `return_wit_1`, use exit arithmetic to prove `i = n - 1`, normalize the final replacement to `app l1 [l[0]]`, and instantiate the postcondition witness with that list.

## 2026-04-19 proof iteration details

- First proof attempt for `rotate_left_by_one_step_list` failed at `sublist_split i n (i + 1) l` with `Cannot find witness`. The side condition needed `Zlength_correct l` in addition to the logical length hypothesis `Zlength l = n`; adding `pose proof (Zlength_correct l); lia` made the rewrite stable.
- The next `rotate_left_by_one_step_list` attempt failed because `replace_Znth_app_r` leaves a prefix term `replace_Znth i ... l1` when the write index equals the prefix length. Rewriting it with `replace_Znth_nothing` using `Zlength l1 = i` fixed the helper.
- The final-list helper initially failed to match `sublist (n - 1) n l` against `sublist_single`'s `sublist m (m + 1) l` shape. I rewrote the sublist endpoint with `replace (sublist (n - 1) n l) with (sublist (n - 1) ((n - 1) + 1) l)` before applying `sublist_single`.
- In `return_wit_1`, after `pre_process` and `subst i_2`, the context was normalized around `Zlength l1`; the final memory term used `sublist (Zlength l1) n_pre l`. Rewriting both `first = Znth 0 l 0` and `Zlength l1 = n_pre - 1` exposed the exact helper-lemma shape.
- `entailer!` produced the return pure goals in the order: shifted-prefix forall, last element, length. The proof script was reordered accordingly and uses `H8 : Zlength l1 = n_pre - 1` for the app-index side conditions.
- After these changes, `rotate_left_by_one_proof_manual.v` compiled successfully, and the full compile sequence through `rotate_left_by_one_goal_check.v` also passed.
