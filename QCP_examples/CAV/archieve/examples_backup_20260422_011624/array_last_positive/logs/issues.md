## Verification Issues

### 1. Missing loop invariant for last-positive prefix state

- Phenomenon: the active annotated file initially had a `for (i = 0; i < n; ++i)` loop with no `Inv`, so symbolic execution would not retain the relation between `ans` and the processed prefix, nor the preserved `IntArray::full(a, n, l)` ownership.
- Trigger: `array_last_positive` scans the array without early return and updates `ans` whenever `a[i] > 0`; the postcondition needs the final `ans` to be the last positive index, or `-1` when no positive exists.
- Location: `annotated/verify_20260420_120451_array_last_positive.c`, immediately before and after the loop.
- Fix: added a conjunctive implication-form invariant: `0 <= i && i <= n`, unchanged `a` and `n`, `-1 <= ans && ans < i`, no-positive prefix fact when `ans == -1`, positive fact when `0 <= ans`, later-prefix nonpositive fact, and `IntArray::full(a, n, l)`. Added a loop-exit `Assert` restating the same facts at `i == n`.
- Result: `symexec` succeeded and generated current `array_last_positive_goal.v`, `array_last_positive_proof_auto.v`, `array_last_positive_proof_manual.v`, and `array_last_positive_goal_check.v`.

### 2. Manual proof obligations remained after symbolic execution

- Phenomenon: generated `array_last_positive_proof_manual.v` contained three admitted manual witnesses: `proof_of_array_last_positive_entail_wit_1`, `proof_of_array_last_positive_entail_wit_3`, and `proof_of_array_last_positive_return_wit_1`.
- Trigger: the remaining obligations were pure entailments connecting initialization, loop exit, and the final disjunctive postcondition.
- Location: `output/verify_20260420_120451_array_last_positive/coq/generated/array_last_positive_proof_manual.v`.
- Fix: filled the witnesses by unfolding the goals, using `entailer!` for simple entailments, deriving `i = n_pre` by `lia` in the loop-exit witness, and splitting `return_wit_1` on `Z.eq_dec ans (-1)`.
- Result: `proof_manual.v` compiles and contains no `Admitted.` or added `Axiom`.

### 3. First manual proof compile attempt used the wrong subgoal order

- Phenomenon: compiling `proof_manual.v` first failed at line 36 with a type mismatch: `Hj : ans < j < n_pre` was supplied where `H4` expected `ans = -1`.
- Trigger: after `entailer!` in `proof_of_array_last_positive_entail_wit_3`, the generated subgoal order differed from the closest `array_find_last_equal` example.
- Location: `proof_of_array_last_positive_entail_wit_3` in `array_last_positive_proof_manual.v`.
- Fix: swapped the two proof branches: the later-index subgoal now applies `H6`, and the no-positive subgoal introduces `Hans` and applies `H4 Hans`.
- Result: rerunning the full compile sequence for `goal`, `proof_auto`, `proof_manual`, and `goal_check` succeeded.

### 4. Coq intermediate cleanup required after successful compilation

- Phenomenon: successful `coqc` runs produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal Coq compilation output.
- Location: `output/verify_20260420_120451_array_last_positive/coq/generated/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory.
- Result: only the four generated `.v` files remain in `coq/generated/`.
