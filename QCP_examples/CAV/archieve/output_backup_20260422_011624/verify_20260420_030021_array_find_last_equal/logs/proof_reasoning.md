## Round 1

- Generated manual obligations: `proof_of_array_find_last_equal_entail_wit_1`, `proof_of_array_find_last_equal_entail_wit_3`, and `proof_of_array_find_last_equal_return_wit_1` in `coq/generated/array_find_last_equal_proof_manual.v`.
- Current state: all three generated manual lemmas are `Admitted.`, so the manual proof file must be completed before `goal_check.v` can count as verified.
- Available context from the generated goals: the loop-exit witness has bounds `i >= n_pre`, `0 <= i`, `i <= n_pre`, accumulator facts for `ans`, and quantified invariant hypotheses over the processed prefix. The return witness has the exit assertion facts over `[0,n)` plus the disjunctive postcondition.
- Proof plan: `entail_wit_1` should close by unfolding and `entailer!`. `entail_wit_3` needs `entailer!`, then an explicit `i = n_pre` fact from arithmetic before applying the invariant quantifier hypotheses. `return_wit_1` needs an explicit split on `ans = -1` so the proof can choose the no-match or match branch of the disjunctive postcondition before using `entailer!`.
- Reuse note: `examples/array_find_last_equal/coq/generated/array_find_last_equal_proof_manual.v` contains a completed proof for the same generated obligation shape. The current workspace has a different Coq logic path in the import line, so only the lemma bodies are reused.
