## 2026-04-21 02:08:51 +0800

After successful `symexec`, `coq/generated/count_divisors_proof_manual.v` contains five manual obligations:

- `proof_of_count_divisors_safety_wit_5`: prove `cnt + 1` is in signed-int range on the divisor branch.
- `proof_of_count_divisors_entail_wit_1`: prove the initial invariant, mainly `count_divisors_prefix n 0 = 0`.
- `proof_of_count_divisors_entail_wit_2_1`: preserve the invariant when `n % d == 0`, so the prefix count for limit `d` is the old prefix count plus one.
- `proof_of_count_divisors_entail_wit_2_2`: preserve the invariant when `n % d != 0`, so the prefix count for limit `d` is unchanged.
- `proof_of_count_divisors_entail_wit_3`: at loop exit, `d > n` and `d <= n + 1` imply `d = n + 1`, and the prefix at limit `n` is exactly `count_divisors_spec n`.

The current proof context has no heap reasoning beyond `emp`, so the planned edit is to add local pure helper lemmas to `count_divisors_proof_manual.v`:

- bounds: `0 <= count_divisors_prefix n limit <= limit` for nonnegative limits, enough for the int safety witness;
- step lemmas for positive `d`, splitting on whether the generated C remainder expression is zero;
- final-prefix lemma unfolding `count_divisors_spec`.

The main witness proofs should then use `pre_process`, unfold the helper definition, rewrite with the step/final lemmas, and finish remaining arithmetic with `lia`.

## 2026-04-21 02:20:33 +0800

Manual proof completed. During proof iteration, the first helper bound lemma failed because `lia` did not automatically normalize `Z.of_nat (S fuel)` after simplification; I fixed it by explicitly changing `Z.pos (Pos.of_succ_nat fuel)` back to `Z.of_nat (S fuel)` and rewriting `Nat2Z.inj_succ`.

The step lemmas also needed explicit normalization of `Z.to_nat d = S (Z.to_nat (d - 1))` and of the generated `Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))` divisor back to `d`; otherwise the recursive `count_divisors_upto` body did not line up with the C loop candidate. In the two loop-preservation witnesses, unrestricted `rewrite count_divisors_prefix_step_*` tried to rewrite the old prefix expression as well, so I changed the proof to assert the step equation separately and rewrite only the new prefix expression.

Final fail-fast compile passed in the documented order:

- `original/count_divisors.v`
- `coq/deps/count_divisors_verify_aux.v`
- `coq/generated/count_divisors_goal.v`
- `coq/generated/count_divisors_proof_auto.v`
- `coq/generated/count_divisors_proof_manual.v`
- `coq/generated/count_divisors_goal_check.v`

`count_divisors_proof_manual.v` now has no `Admitted.` and no locally added `Axiom`.
