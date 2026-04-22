## 2026-04-20 proof pass 1

After successful `symexec`, `coq/generated/tribonacci_proof_manual.v` contains six admitted manual obligations:

- `proof_of_tribonacci_safety_wit_9`
- `proof_of_tribonacci_safety_wit_10`
- `proof_of_tribonacci_entail_wit_1`
- `proof_of_tribonacci_entail_wit_2`
- `proof_of_tribonacci_return_wit_1`
- `proof_of_tribonacci_return_wit_2`

The generated goals in `tribonacci_goal.v` show the following proof shape:

- `safety_wit_9` proves signed-int range for `(a + b) + c` inside the loop, using the invariant facts `a = tribonacci_z(i - 3)`, `b = tribonacci_z(i - 2)`, `c = tribonacci_z(i - 1)`, and bounds `3 <= i <= n_pre <= 37`.
- `safety_wit_10` proves signed-int range for the partial sum `a + b` under the same invariant facts.
- `entail_wit_1` proves loop-invariant initialization at `i = 3`, namely `tribonacci_z(0)=0`, `tribonacci_z(1)=1`, and `tribonacci_z(2)=1`.
- `entail_wit_2` proves loop-invariant preservation after storing `d = a + b + c` and shifting the accumulators. It needs the tribonacci recurrence and the standard weakening from `d |-> value` to `d |->_`.
- `return_wit_1` and `return_wit_2` prove the early-return cases for `n = 0` and `n = 1`.

The imported `tribonacci.v` defines `tribonacci_z` by computation through `tribonacci_triple`, but it has no recurrence or range lemmas. Following the successful Fibonacci proof pattern, I will add local helper lemmas directly in `tribonacci_proof_manual.v`: a recurrence lemma for `tribonacci_nat`, a lifted `tribonacci_z_step` lemma for `z >= 3`, and small finite-range lemmas for indices `0..37` / loop indices `3..37`. These avoid modifying the input contract file and keep the main witness proofs focused on rewriting and separation-logic framing.

## 2026-04-20 proof pass 2

First compile attempt:

- `original/tribonacci.v`, `tribonacci_goal.v`, and `tribonacci_proof_auto.v` compiled.
- `tribonacci_proof_manual.v` failed at line 29 in `tribonacci_nat_step`.
- Error text: `Expects a disjunctive pattern with 3 branches.`

Cause: I first destructed `tribonacci_triple n` as `[a [b c]]`, assuming right-nested pair notation. Changing it to `[a b c]` parsed, but Coq warned that `c` was unused and the simplified goal did not reduce to arithmetic, then failed with `Cannot find witness.` A focused `coqtop` probe showed that `tribonacci_triple` has shape `(Z * Z) * Z`, so the stable pattern is `[[a b] c]`. I will use that nested-left destruct and rerun the same compile order.

## 2026-04-20 proof pass 3

After fixing `tribonacci_nat_step`, compilation progressed to `proof_of_tribonacci_entail_wit_2` and failed on the third pure subgoal:

- file: `coq/generated/tribonacci_proof_manual.v`
- line: 122
- error: `Unable to unify "tribonacci_z (i + 1 - 1)" with "tribonacci_z (i - 3) + b + c".`

This is not an annotation issue: the invariant facts `a = tribonacci_z (i - 3)`, `b = tribonacci_z (i - 2)`, and `c = tribonacci_z (i - 1)` are present. The problem is proof-script direction: using `rewrite H2 in *; rewrite H3 in *; rewrite H4 in *` globally can rewrite hypotheses and target fragments in a brittle order. I will rewrite only the active goal after normalizing `(i + 1 - 1)` to `i`, then use `tribonacci_z_step i` and close by associativity/arithmetic.

The immediate next compile still failed at line 122, but this time the line was the first preservation bullet. I had used `H2` (`a = T(i-3)`) to prove the shifted `b = T((i+1)-3)` obligation. That is the wrong accumulator: after the loop body shift, the new `a` slot contains old `b`, so the first bullet must use `H3`; the second shifted obligation must use `H4`.

A `coqtop` inspection of the state after `pre_process; sep_apply store_int_undef_store_int; entailer!` showed that the remaining pure goals are ordered as:

1. `a + b + c = tribonacci_z (i + 1 - 1)`
2. `c = tribonacci_z (i + 1 - 2)`
3. `b = tribonacci_z (i + 1 - 3)`

So the proof bullets must follow this generated order, not the textual invariant order. I will put the recurrence proof first, then the `c` and `b` shifted accumulator goals.

The reordered proof then failed on `rewrite tribonacci_z_step by lia` with `Cannot find witness`. The rewrite tactic was matching the first available `tribonacci_z _` subterm, such as `tribonacci_z (i - 3)`, and trying to prove the side condition for that subterm. The intended recurrence is only for index `i`. I will first pose `tribonacci_z_step i H0` as a named equality and rewrite with that equality, which targets `tribonacci_z i` directly.

## 2026-04-20 proof completion

After posing the recurrence fact explicitly as `Hstep : tribonacci_z i = tribonacci_z (i - 3) + tribonacci_z (i - 2) + tribonacci_z (i - 1)`, `tribonacci_proof_manual.v` compiled successfully.

Final manual proof structure:

- `tribonacci_nat_step` proves the recurrence by destructing `tribonacci_triple n` as `[[a b] c]`.
- `tribonacci_z_step` lifts that recurrence to `Z` indices with `z >= 3`.
- `tribonacci_z_triple_sum_int_bound_3_37` and `tribonacci_z_pair_sum_int_bound_3_37` discharge the signed-int overflow side conditions by finite computation over loop indices `3..37`.
- `safety_wit_9` and `safety_wit_10` rewrite accumulator values from the loop invariant and invoke those bound lemmas.
- `entail_wit_1` is closed by `pre_process`.
- `entail_wit_2` uses `store_int_undef_store_int`, then proves the generated pure goals in their actual order: recurrence sum, shifted `c`, shifted `b`.
- `return_wit_1` and `return_wit_2` substitute `n_pre = 0` / `n_pre = 1` and close by computation/reflexivity.

The full compile replay then passed for `original/tribonacci.v`, `tribonacci_goal.v`, `tribonacci_proof_auto.v`, `tribonacci_proof_manual.v`, and `tribonacci_goal_check.v`. `tribonacci_proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
