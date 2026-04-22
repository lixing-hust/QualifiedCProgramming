# Proof Reasoning

## Round 1

- `symexec` succeeded on the latest annotated file and generated one manual obligation: `proof_of_array_has_adjacent_equal_return_wit_2`.
- Witness shape: this is the final `return 0` path. The assumptions include `i_3 >= n_pre`, `1 <= i_3`, `i_3 <= n_pre + 1`, the invariant universal `(forall j, 1 <= j /\ j < i_3 -> Znth j l 0 <> Znth (j - 1) l 0)`, `0 <= n_pre`, `Zlength l = n_pre`, and `IntArray.full a_pre n_pre l`.
- Goal shape: prove the disjunction in the postcondition. The right branch is impossible because it contains `0 = 1`; the intended branch is the left one with `0 = 0`, the full-range universal over `1 <= i < n_pre`, and unchanged array ownership.
- Planned proof: run `pre_process`, choose the left disjunct, use `entailer!` for the separation part and trivial equality, then prove the universal by applying the invariant to the same index. The only bridge is arithmetic: from `i < n_pre` and `i_3 >= n_pre`, derive `i < i_3` by `lia`.

## Round 2

- Compile failure: `compile_proof_manual.log` reported `No product even after head-reduction` at the line `intros i [? ?]` in `proof_of_array_has_adjacent_equal_return_wit_2`.
- Interpretation: after `pre_process`, selecting the left disjunct, and running `entailer!`, Coq no longer has a universal-introduction goal at that point. The automation has already consumed the invariant and arithmetic context for the remaining pure side condition.
- Repair: remove the trailing manual `intros/apply/lia` block and leave the proof as `pre_process; left; entailer!`.

## Round 3

- `coqtop` showed the remaining post-`entailer!` goal is not a Coq product but a model-level assertion conjunction: `([|0 = 0|] && ([|forall i, ...|] && IntArray.full ...)) m`.
- Therefore the right proof shape is to unfold the witness, run `Intros`, select the left disjunct, run `entailer!`, then split the model-level assertion conjunction explicitly.
- The universal proof subgoal then has hypotheses `H : i_3 >= n_pre` and `H2 : forall j, 1 <= j < i_3 -> ...`; for an arbitrary `i` satisfying `1 <= i < n_pre`, applying `H2` is justified by `lia`.
- I verified this exact script in `coqtop`; next step is to patch `proof_manual.v` and rerun the full compile chain.
