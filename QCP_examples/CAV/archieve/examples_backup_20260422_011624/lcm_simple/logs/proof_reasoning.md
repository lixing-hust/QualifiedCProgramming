## 2026-04-21 proof pass 1

Fresh `symexec` succeeded and generated four manual obligations in `coq/generated/lcm_simple_proof_manual.v`: `proof_of_lcm_simple_entail_wit_1`, `proof_of_lcm_simple_entail_wit_2`, `proof_of_lcm_simple_entail_wit_3`, and `proof_of_lcm_simple_return_wit_1`.

The obligations are pure arithmetic entailments. `entail_wit_1` initializes the invariant at `x = a_pre`, including `a_pre <= Z.lcm a_pre b_pre`, `a_pre % a_pre = 0`, the implication that the next multiple is within the lcm when `a_pre` is not divisible by `b_pre`, and the vacuous "no smaller positive multiple of a is b-divisible" fact. `entail_wit_2` preserves the invariant after `x = x + a_pre`; the key facts are that `x + a_pre` remains a multiple of `a_pre`, no positive multiple of `a_pre` lies strictly between `x` and `x + a_pre`, and if the new value is still not divisible by `b_pre`, another `a_pre` step remains within `Z.lcm a_pre b_pre`. `entail_wit_3` proves the loop-exit bridge `x = lcm_simple_value a_pre b_pre`; it needs the standard `Z.lcm_least` property plus the invariant's `x <= lcm` bound. `return_wit_1` should close by unfolding `lcm_simple_spec` and `lcm_simple_value`.

The first proof edit will add local helper lemmas for positive lcm bounds, converting C remainder facts to divisibility, the "next multiple before lcm" range fact, and the absence of a distinct multiple between consecutive multiples. Then each witness can use `pre_process`, `entailer!`, these helpers, and `lia`/`unfold` rather than embedding all arithmetic directly in the witness bodies.

## 2026-04-21 proof pass 2

The first regenerated manual proof after the post-loop assertion contained three obligations: `entail_wit_1`, `entail_wit_2`, and `return_wit_1`. I added helper lemmas directly in `lcm_simple_proof_manual.v`:
- `lcm_simple_rem_mod_pos`, `lcm_simple_rem_zero_divide_pos`, and `lcm_simple_divide_rem_zero_pos` bridge generated C remainder notation to standard divisibility facts.
- `lcm_simple_lcm_pos`, `lcm_simple_a_le_lcm`, and `lcm_simple_lcm_rem_b` package the positive-input facts about `Z.lcm`.
- `lcm_simple_consecutive_multiple` proves there is no distinct multiple of `a` in `[x, x+a)`.
- `lcm_simple_step_rem_a` proves the loop body preserves divisibility by `a`.
- `lcm_simple_next_within_lcm` proves the range bridge used for `x + a`.
- `lcm_simple_exit_eq` proves that a positive common multiple bounded above by the lcm is equal to the lcm.

The main compile iteration issues were:
- `proof_of_lcm_simple_entail_wit_1`: after `entailer!`, the generated subgoal order was `forall`, then next-step implication, then `a % a = 0`, then `a <= lcm`. I reordered the proof bullets to match that state.
- `proof_of_lcm_simple_entail_wit_2`: after `entailer!`, the subgoal order was the quantified preservation fact, then the next-step implication, then `(x+a) % a = 0`. I used `lcm_simple_consecutive_multiple` in the quantified case and `lcm_simple_step_rem_a` for the modulo fact.
- `proof_of_lcm_simple_return_wit_1`: a compile against freshly rebuilt `goal.v` showed that `pre_process` alone left open goals. The final proof unfolds `lcm_simple_spec`, runs `entailer!`, and applies `lcm_simple_exit_eq`.

After these edits, `lcm_simple_proof_manual.v` compiled successfully. The full documented replay then compiled `original/lcm_simple.v`, `lcm_simple_goal.v`, `lcm_simple_proof_auto.v`, `lcm_simple_proof_manual.v`, and `lcm_simple_goal_check.v`. A final grep found no `Admitted.` and no top-level `Axiom` in `lcm_simple_proof_manual.v`.
