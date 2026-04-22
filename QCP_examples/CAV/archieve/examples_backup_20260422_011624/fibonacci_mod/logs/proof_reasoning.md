## 2026-04-21 03:50:12 CST - first manual proof plan

Fresh `symexec` succeeded and generated `coq/generated/fibonacci_mod_goal.v`, `fibonacci_mod_proof_auto.v`, `fibonacci_mod_proof_manual.v`, and `fibonacci_mod_goal_check.v`.

`fibonacci_mod_proof_manual.v` contains three admitted obligations:

- `proof_of_fibonacci_mod_entail_wit_1`: initialize the loop invariant from the nonzero branch. The pure gaps are `fib_mod_z 0 mod = 0`, `fib_mod_z 1 mod = 1 % mod`, and basic positive-modulo range facts.
- `proof_of_fibonacci_mod_entail_wit_2`: preserve the loop invariant after one Fibonacci update. The pure gap is the recurrence `fib_mod_z (k + 2) m = (fib_mod_z k m + fib_mod_z (k + 1) m) % m` for `k >= 0`, plus modulo range facts and the stack slot for `c` becoming undefined.
- `proof_of_fibonacci_mod_return_wit_1`: prove the early return for `n == 0`, which should reduce to `fib_mod_z 0 mod = 0`.

The proof should add local helper lemmas in the manual file only, with no new axioms: base cases for `fib_mod_z`, a one-step recurrence derived from `fib_mod_pair`, and then short witness proofs using `pre_process`, `entailer!`, `lia`, and `Z.rem_*` lemmas.

## 2026-04-21 03:50:44 CST - first compile failure

Compiling `coq/generated/fibonacci_mod_proof_manual.v` failed at line 30:

`Error: Unknown scope delimiting key m.`

The cause is that `Local Open Scope sac` makes the `%` notation in my helper lemma statement `fib_mod_z 1 m = 1 % m` ambiguous; Coq reads `% m` as a scope delimiter rather than binary remainder notation. The generated goals already parsed, but local helper statements should avoid this notation. I will rewrite helper lemmas to use explicit `Z.rem` in statements and recurrence conclusions.

## 2026-04-21 03:51:21 CST - entailer subgoal order

After the helper notation fix, `coqc` failed in `proof_of_fibonacci_mod_entail_wit_1` with:

`Error: Found no subterm matching "fib_mod_z 0 ?M13717" in the current goal.`

Using `coqtop` after `pre_process; entailer!` showed that `entail_wit_1` leaves only two modulo range goals, in this order: `1 % mod_pre < mod_pre`, then `0 <= 1 % mod_pre`. The Fibonacci base equalities are already discharged by simplification/automation. For `entail_wit_2`, `coqtop` shows the remaining order is recurrence equality, shifted `b` equality, modulo upper bound, modulo lower bound. I will reorder the bullets to match the actual proof state.

## 2026-04-21 03:51:55 CST - recurrence index normalization

The reordered proof then failed at `proof_manual.v` line 79:

`Error: Found no subterm matching "fib_mod_z (i - 1) mod_pre" in the current goal.`

After rewriting with the recurrence lemma, the second recursive term remains syntactically `fib_mod_z (i - 2 + 1) mod_pre`, so `rewrite <- H7` cannot match `H7 : b = fib_mod_z (i - 1) mod_pre`. I will insert an explicit `replace ((i - 2) + 1) with (i - 1) by lia` before rewriting with `H7`.

## 2026-04-21 03:52:22 CST - early return branch normalization

The next compile failure is in `proof_of_fibonacci_mod_return_wit_1`:

`Error: Found no subterm matching "fib_mod_z 0 ?M4187" in the current goal.`

The return goal still contains `fib_mod_z n_pre mod_pre` even though the branch hypothesis has `n_pre = 0`. I will `subst n_pre` before rewriting with `fib_mod_z_0_local`.
