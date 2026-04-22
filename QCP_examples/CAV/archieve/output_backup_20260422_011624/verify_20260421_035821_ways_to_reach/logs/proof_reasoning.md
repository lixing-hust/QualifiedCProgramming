## Iteration 1: generated recurrence obligations after successful symexec

Timestamp: 2026-04-21 04:01:02 +0800

Fresh `symexec` succeeded on the latest annotated file and generated:

- `coq/generated/ways_to_reach_goal.v`
- `coq/generated/ways_to_reach_proof_auto.v`
- `coq/generated/ways_to_reach_proof_manual.v`
- `coq/generated/ways_to_reach_goal_check.v`

The generated manual proof file contains four admitted obligations:

- `proof_of_ways_to_reach_safety_wit_6`: loop-body overflow safety for
  `c = a + b`
- `proof_of_ways_to_reach_entail_wit_1`: initialization of the loop invariant
  after the `n != 0` branch
- `proof_of_ways_to_reach_entail_wit_2`: preservation of the shifted recurrence
  invariant after one loop body iteration
- `proof_of_ways_to_reach_return_wit_1`: early return proof for `n == 0`

The close repository example `CAV/examples/fibonacci` uses the same pair-state
recurrence proof pattern. This task differs only in the recurrence base pair:
`ways_to_reach_pair 0 = (1, 1)` instead of `fib_pair 0 = (0, 1)`, and the input
bound is `n <= 45`. I will add local helper lemmas directly in
`ways_to_reach_proof_manual.v`:

- a natural-number step lemma for `ways_to_reach_nat`
- a `Z`-indexed recurrence lemma
- a finite split/bound lemma for indices `0..45`

Then the witness proofs should follow the existing pattern:

- `safety_wit_6`: rewrite `a + b` to `ways_to_reach_z i`, apply the finite bound,
  and solve with `lia`
- `entail_wit_1`: use `pre_process` to simplify the base cases
- `entail_wit_2`: first consume the local `c` store with
  `store_int_undef_store_int`, then prove the shifted accumulator equalities
- `return_wit_1`: substitute `n_pre = 0` and reduce the base case
