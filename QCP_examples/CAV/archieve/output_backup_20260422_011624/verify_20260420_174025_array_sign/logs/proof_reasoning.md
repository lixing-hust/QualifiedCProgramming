## 2026-04-20 retry: manual proof after split implication symexec

After the successful `symexec` run at `2026-04-20 18:16:27 CST`, the generated manual file contains exactly one admitted theorem: `proof_of_array_sign_entail_wit_1`. The corresponding VC in `array_sign_goal.v` is the loop-invariant initialization entailment from the function precondition. It asks for witnesses `l1` and `l2` such that `Zlength l1 = 0`, `Zlength l2 = n_pre - 0`, the three processed-prefix implications hold for indices `< 0`, the suffix relation matches `lo`, and `IntArray.full out_pre n_pre (app l1 l2)` matches the original output array.

Available assumptions are `0 <= n_pre`, `Zlength la = n_pre`, `Zlength lo = n_pre`, and the two full-array resources. The correct witnesses are `l1 = nil` and `l2 = lo`. With those witnesses, the prefix implications are vacuous by `t < 0`, the suffix relation reduces to `Znth t lo 0 = Znth (0 + t) lo 0`, and the spatial output resource reduces by `app nil lo = lo`.

Planned proof change: replace the generated `Admitted.` in `array_sign_proof_manual.v` with an explicit proof that unfolds `array_sign_entail_wit_1`, introduces the precondition, chooses `lo` and `nil`, simplifies `app nil lo`, and lets `entailer!`/`lia` discharge the pure side conditions, with a direct rewrite for the suffix equality.

First compile result: `array_sign_goal.v` and `array_sign_proof_auto.v` compiled, but `array_sign_proof_manual.v` failed at line 28 with `Wrong bullet -: No more goals.` This means `Exists lo nil; simpl; entailer!` already solved the entailment completely, and the explicit bullet subproofs were stale. Next change: remove the unnecessary bullets and keep the minimal proof script.
