# Proof Reasoning

## Round 1

- Fresh `symexec` succeeded for `annotated/verify_20260421_045730_count_multiples.c` and generated `count_multiples_goal.v`, `count_multiples_proof_auto.v`, `count_multiples_proof_manual.v`, and `count_multiples_goal_check.v`.
- Manual obligations in `count_multiples_proof_manual.v`:
  - `proof_of_count_multiples_entail_wit_1`: initialize the loop invariant. The only nontrivial pure fact is `0 = count_multiples_spec (1 - 1) k_pre`, which should reduce to `count_multiples_spec 0 k_pre = 0`.
  - `proof_of_count_multiples_entail_wit_2_1`: preserve the invariant through the divisible branch. Given `i % k_pre = 0` and `cnt = count_multiples_spec (i - 1) k_pre`, the proof must show `cnt + 1 = count_multiples_spec i k_pre`.
  - `proof_of_count_multiples_entail_wit_2_2`: preserve the invariant through the non-divisible branch. Given `i % k_pre <> 0` and `cnt = count_multiples_spec (i - 1) k_pre`, the proof must show `cnt = count_multiples_spec i k_pre`.
- Current proof gap: the generated goals use the C `%` branch fact while the specification unfolds through `count_multiples_upto` and `Z.rem`. The main witnesses should stay short, so I will add local helper lemmas in `proof_manual.v` for the zero case and the one-step spec update, then use `pre_process; entailer!` plus those lemmas in the three witnesses.
- No manual proof should add `Axiom` or leave `Admitted.`.

## Round 2

- First compile attempt reached `count_multiples_proof_manual.v` and failed at line 85 with `Error: No such goal.`
- Localization: `proof_of_count_multiples_entail_wit_1`.
- Diagnosis: `pre_process` already discharged the invariant initialization witness, including the zero-case simplification for `count_multiples_spec (1 - 1) k_pre`; the following `entailer!` was being applied after the proof state had no remaining goals.
- Next edit: trim `proof_of_count_multiples_entail_wit_1` to just `pre_process.` and rerun the compile chain.
