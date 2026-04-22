# Proof Reasoning

## Iteration 1: Reuse prefix-count proof pattern with parity branch

- Current generated manual obligations:
  - `proof_of_array_count_even_safety_wit_6`
  - `proof_of_array_count_even_entail_wit_1`
  - `proof_of_array_count_even_entail_wit_2_1`
  - `proof_of_array_count_even_entail_wit_2_2`
  - `proof_of_array_count_even_entail_wit_3`
- Current blocker:
  - `array_count_even_proof_manual.v` contains five generated `Admitted.` placeholders, so `goal_check.v` cannot be accepted under the verify completion rules.
- Available context from `array_count_even_goal.v`:
  - the loop invariant gives `cnt = array_count_even_spec (sublist 0 i l)`, `0 <= i`, `i <= n_pre`, `i < n_pre` inside the loop, `Zlength l = n_pre`, and the preserved `IntArray.full a_pre n_pre l`
  - the true branch additionally has `(Znth i l 0) % 2 = 0`; the false branch has `(Znth i l 0) % 2 <> 0`
- Reusable pattern:
  - `examples/array_count_zero/coq/generated/array_count_zero_proof_manual.v` proves the same prefix-count invariant shape using a spec append-single lemma, a spec bounds lemma, and sublist splitting at `i`
- Planned proof edit:
  - add `array_count_even_spec_app_single` to rewrite the spec over `sublist 0 (i + 1) l` as the previous prefix plus the current element
  - add `array_count_even_spec_bounds` to prove `0 <= cnt <= i`, which supplies the integer range proof for `cnt + 1`
  - use `pre_process`, `entailer!`, `lia`, `sublist_split`, and `sublist_single` in the five witness proofs

## Iteration 2: Stabilize the true branch parity case split

- First compile failure:
  - file: `coq/generated/array_count_even_proof_manual.v`
  - location: line 84 in `proof_of_array_count_even_entail_wit_2_1`
  - error: `Tactic failure: Cannot find witness.`
- Diagnosis:
  - after rewriting the true-branch hypothesis `Z.rem (Znth i l 0) 2 = 0`, the proof should destruct the normalized decision `Z.eq_dec 0 0`, matching the stable `array_count_zero` proof pattern
  - destructing the original decision expression left automation with a less normalized arithmetic/separation state
- Planned edit:
  - change the true branch proof to `rewrite H; destruct (Z.eq_dec 0 0); lia`
  - rerun the compile chain with shell fail-fast so Coq failures are reflected in the command status
