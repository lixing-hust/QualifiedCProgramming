## Round 1: manual obligations after successful symexec

Fresh `symexec` succeeded on the active annotated file and generated five admitted manual obligations in `coq/generated/reverse_digits_proof_manual.v`: `proof_of_reverse_digits_safety_wit_3`, `proof_of_reverse_digits_safety_wit_5`, `proof_of_reverse_digits_entail_wit_1`, `proof_of_reverse_digits_entail_wit_2`, and `proof_of_reverse_digits_entail_wit_3`.

The goal shapes in `reverse_digits_goal.v` show that all five are pure arithmetic or pure helper-unfolding obligations. The central invariant is `reverse_digits_acc_z n ans = reverse_digits_z n_pre`, where `reverse_digits_acc_z` hides the `Z.to_nat` fuel conversion. Loop preservation needs a positive-step lemma:

- for `n > 0`, `reverse_digits_acc_z n ans = reverse_digits_acc_z (n ÷ 10) (ans * 10 + n % 10)`;
- for exit, `reverse_digits_acc_z 0 ans = ans`;
- for overflow safety, `ans * 10 + n % 10 <= reverse_digits_acc_z n ans` after the step, and therefore the precondition bound on `reverse_digits_z n_pre` bounds the C assignment.

The proof script will add local helper lemmas analogous to the completed `digit_sum` proof: quotient decrease/nonnegativity, positive remainder bounds, fuel stability beyond `Z.to_nat`, one-step unfolding, and accumulator monotonicity. Then the witness proofs can remain short: `pre_process`, `entailer!`, rewrite the invariant through the step lemma, and finish arithmetic with `lia`.

## Round 2: stabilize induction hypothesis name

First compile replay failed in `reverse_digits_proof_manual.v` at line 153 with `Error: The variable IHfuel was not found in the current environment.` This is a proof-script stability issue in helper lemma `reverse_digits_fuel_acc_ge`: the script used the automatically chosen induction hypothesis name after `induction fuel`, but this Coq environment did not bind it as `IHfuel`. I will rewrite that induction as `induction fuel as [|fuel IH]` and call `IH` explicitly.

The next compile showed this Coq version rejects the newer `induction ... as [|fuel IH]` intro-pattern syntax at line 145. I will keep the older `induction fuel` form and avoid depending on the generated name by finding the induction hypothesis with a `match goal` pattern.

That pattern still mentioned the post-induction fuel variable by name, and the actual generated name was different, producing `The reference fuel was not found`. I will make the `match goal` pattern use a metavariable for the recursive fuel argument instead of a concrete identifier.

The later direct `IHfuel` compile still failed because the base case `acc <= acc` had not been discharged before the `destruct (Z.leb n 0)` step, so the script was destructing the base goal where no induction hypothesis exists. I will explicitly close trivial goals with `all: try lia` immediately after the induction line, then use `IHfuel` in the actual successor branch.

The next compile reached `proof_of_reverse_digits_safety_wit_3` and failed on the lower-bound branch with `Cannot find witness`. The remaining goal is the signed lower bound for `ans * 10 + n % 10`; the context gives nonnegativity, but the generated `INT_MIN` constant is not normalized for `nia`. I will explicitly normalize `Int.min_signed` and `Int.max_signed` in the affected arithmetic branches before calling `nia`/`lia`.

A `coqtop` inspection showed that after `entailer!`, the pure conjunct goals are produced in the reverse order from the displayed entailment: the signed lower-bound goal appears before the upper-bound goal. My first script put the semantic step proof in the first bullet and the simple nonnegativity proof in the second bullet, so the second bullet was actually trying to prove the upper bound without the invariant-step lemma. I will swap the safety witness bullets so lower bounds are handled first and upper bounds use `reverse_digits_acc_z_step` plus accumulator monotonicity.

The next compile reached `reverse_digits_entail_wit_2`; `coqtop` shows the five generated subgoals after `entailer!` are: semantic step equality, next accumulator upper bound, next accumulator nonnegativity, quotient upper bound, and quotient nonnegativity. I will reorder the proof bullets to match that concrete order instead of the textual order in `goal.v`.
