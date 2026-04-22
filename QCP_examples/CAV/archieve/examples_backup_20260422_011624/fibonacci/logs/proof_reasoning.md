## Iteration 1: manual obligations after successful symexec

After `symexec` succeeded, `coq/generated/fibonacci_proof_manual.v` contained four admitted obligations:

- `proof_of_fibonacci_safety_wit_6`
- `proof_of_fibonacci_entail_wit_1`
- `proof_of_fibonacci_entail_wit_2`
- `proof_of_fibonacci_return_wit_1`

I compiled the current generated files before editing the proof:

- `original/fibonacci.v` compiled
- `fibonacci_goal.v` compiled
- `fibonacci_proof_auto.v` compiled
- `fibonacci_proof_manual.v` compiled only because these four obligations were still `Admitted.`

The goal shapes in `fibonacci_goal.v` show that all four manual obligations are pure arithmetic or pure `fib_z` computation:

- `safety_wit_6` must prove that `a + b` stays in signed-int range when `a = fib_z(i - 2)`, `b = fib_z(i - 1)`, `2 <= i`, `i <= n_pre`, and `n_pre <= 46`.
- `entail_wit_1` must prove loop invariant initialization, including `fib_z(0) = 0` and `fib_z(1) = 1`.
- `entail_wit_2` must prove invariant preservation after the Fibonacci update, including the bounded recurrence from `fib_z(i - 2) + fib_z(i - 1)` to `fib_z(i)`.
- `return_wit_1` must prove the early `n == 0` branch returns `fib_z(0)`.

The input helper `fibonacci.v` defines `fib_z` by computation but does not provide recurrence or monotonicity lemmas. Because the contract bounds all loop indices by `46`, the conservative proof plan is:

- use `pre_process` / `entailer!` for the separation-logic shell
- discharge `fib_z(0)` and `fib_z(1)` by computation
- for obligations involving an arbitrary loop index, derive that the index is one of `2 .. 46` using `lia`
- finish each bounded Fibonacci arithmetic case with `vm_compute; lia`

This keeps the proof local to the generated manual file and does not require modifying the input Coq contract file.

## Iteration 2: first compile failure in `safety_wit_6`

The first proof edit failed while compiling `fibonacci_proof_manual.v`:

- file: `coq/generated/fibonacci_proof_manual.v`
- line: the call to the local bounded Fibonacci tactic in `proof_of_fibonacci_safety_wit_6`
- error: `Tactic failure: Cannot find witness.`

A `coqtop` probe showed that after `pre_process; entailer!`, `safety_wit_6` leaves two pure goals:

- `-2147483648 <= a + b`
- `a + b <= 2147483647`

with hypotheses `a = fib_z(i - 2)`, `b = fib_z(i - 1)`, `2 <= i`, `i <= n_pre`, and `n_pre <= 46`.
The local tactic was matching a `fib_z` subterm such as `i - 2` instead of splitting on the loop index `i`, so it tried to prove the wrong finite range.

I will change the proofs to explicitly rewrite `a` and `b`, split on the loop index `i` using the `2 .. 46` range, and solve each concrete Fibonacci case by computation.

For `entail_wit_2`, `coqtop` also showed an initial heap goal:

- `&( "c") # Int |-> (a + b) |-- &( "c") # Int |->_`

That goal is exactly the store-to-undef weakening, so the proof should apply `store_int_undef_store_int` before discharging the remaining pure recurrence goals.

The next compile still failed at the same bounded tactic because the disjunction destruct did not reliably substitute the loop index in every branch. I will make the local splitter destruct only facts of the shape `i = constant \/ ...` and explicitly run `subst i` in each equality branch before computation.

Another focused `coqtop` check showed that after `vm_compute`, true `Z` inequalities are reduced to a decidable-comparison form such as `Lt = Gt -> False`. `lia` does not close that reduced constructor-discrimination goal. The bounded tactic therefore needs to try `discriminate` and `reflexivity` after computation, with `lia` only as a fallback.

The next compile showed `No such goal` immediately after `entailer!` in `entail_wit_1`, which means the standard tactic already solved the loop-initialization witness. I will leave that witness as `pre_process; entailer!` and keep custom computation only for obligations that actually remain after `entailer!`.

The exact behavior is even stronger in this generated context: `pre_process` alone closes `entail_wit_1`, so the proof must stop there to avoid running a tactic on an empty proof state.

The next compile moved to `entail_wit_2` and failed with `Nothing to rewrite` on the shared `all: rewrite H2 in *; rewrite H3 in *` line. This happens because the heap weakening subgoal does not contain the accumulator equalities in the same shape as the pure Fibonacci subgoals. The rewrite step should be guarded with `try`, then the bounded computation should run only on remaining pure goals.

That guarded finite-split proof then caused `coqc` to run for more than two minutes in `fibonacci_proof_manual.v`, so I stopped that compile attempt. The problem is proof-search and proof-term size from repeatedly splitting the loop index inside generated VC contexts.

I will replace the broad finite-split tactic with small helper lemmas:

- `fib_nat_step` proves the Fibonacci recurrence over `nat` directly from `fib_pair`.
- `fib_z_step` lifts the recurrence to any `z >= 2`.
- `fib_z_int_bound_0_46` is the only finite table lemma, isolated outside the generated VC context, proving that `fib_z z` is in signed-int range for `0 <= z <= 46`.

Then `safety_wit_6` can rewrite `a + b` to `fib_z i` and use the bound lemma, while `entail_wit_2` can use the recurrence and simple index arithmetic without repeatedly splitting inside the witness proof.

The first compile of the helper-lemma version failed because `INT_MIN` / `INT_MAX` are not available as names in the manual proof context even though generated goals print their numeric values after preprocessing. I will state the local bound lemma with the concrete signed-int limits `-2147483648` and `2147483647`, matching the generated goals.

After that fix, compilation reached `return_wit_1`. A `coqtop` probe showed the remaining goal after `pre_process; entailer!` is exactly `0 = fib_z n_pre` with hypothesis `n_pre = 0`. The stable proof is to substitute `n_pre` and close by computation/reflexivity.
