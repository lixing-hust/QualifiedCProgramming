# Proof Reasoning

## Round 1

- Read `count_positive_goal.v`, `count_positive_proof_auto.v`, and `count_positive_goal_check.v`.
- Manual obligations generated in `count_positive_proof_manual.v`:
  - `proof_of_count_positive_safety_wit_4`
  - `proof_of_count_positive_entail_wit_1`
  - `proof_of_count_positive_entail_wit_2_1`
  - `proof_of_count_positive_entail_wit_2_2`
  - `proof_of_count_positive_entail_wit_3`
- First hypothesis:
  - `entail_wit_1` should be trivial after `entailer!`.
  - `entail_wit_2_1` and `entail_wit_2_2` should follow the same pattern as `count_equal_to_k`: split `sublist 0 (i + 1) l` into the old prefix plus one element, then simplify `count_positive_spec` on the singleton suffix using the branch fact `Znth i l 0 > 0` or `<= 0`.
  - `entail_wit_3` should only need `i = n_pre` from the exit bounds and then `sublist 0 n_pre l = l`.
  - `safety_wit_4` should be arithmetic once the proof explicitly recovers the integer range for `n_pre` and the prefix-count bound `0 <= cnt <= i`.
- Planned proof style:
  - add one helper lemma for `count_positive_spec (l ++ [x])`
  - add one helper lemma bounding `count_positive_spec` by list length
  - keep each witness proof short and compile-driven

## Round 2

- First stable compile failure: `proof_of_count_positive_safety_wit_4` remained incomplete after a plain `entailer!`.
- Diagnosis:
  - the prefix-count bound `0 <= cnt <= i` was necessary but not sufficient by itself
  - the proof also needed the stored integer range for `n_pre` to derive `cnt + 1 <= INT_MAX`
- Fix:
  - switch this witness to `pre_process`
  - use `store_int_range (&("n")) n_pre`
  - derive the arithmetic side conditions explicitly before the final `entailer!`

## Round 3

- The next failure in `entail_wit_2_1` was not a semantic gap.
- Diagnosis:
  - after rewriting the one-step prefix extension, the branch fact was already available as a pure inequality
  - trying to `rewrite H` assumed the wrong proof-state shape and failed because the goal no longer contained a matching `Z_gt_dec` test
- Fix:
  - drop the fragile rewrite
  - finish the branch by destructing `Z_gt_dec (Znth i l 0) 0` directly and discharging the contradiction with `lia`

## Round 4

- The final blocker was `entail_wit_3`.
- Diagnosis:
  - compile output showed the post-`entailer!` goal had already simplified to:
    - `cnt = count_positive_spec l`
  - the remaining proof only needed:
    - `i = n_pre`
    - `cnt = count_positive_spec (sublist 0 n_pre l)`
    - `Zlength l = n_pre`
- Fix:
  - inspect the real proof state with `coqtop`
  - rewrite with the generated equalities `H2` and `H4`
  - normalize `sublist 0 (Zlength l) l` using `sublist_self`
- Result:
  - `count_positive_proof_manual.v` compiled
  - `count_positive_goal_check.v` compiled
