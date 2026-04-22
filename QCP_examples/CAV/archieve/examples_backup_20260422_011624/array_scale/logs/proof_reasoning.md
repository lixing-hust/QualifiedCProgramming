## 2026-04-19 23:37:48 +0800

`symexec` succeeded on the latest annotated file and generated `array_scale_goal.v`, `array_scale_proof_auto.v`, `array_scale_proof_manual.v`, and `array_scale_goal_check.v`. The manual file contains four admitted lemmas: `proof_of_array_scale_safety_wit_2`, `proof_of_array_scale_entail_wit_1`, `proof_of_array_scale_entail_wit_2`, and `proof_of_array_scale_return_wit_1`.

The generated goals match the existing verified `array_add` prefix/tail pattern with multiplication by the scalar `k_pre` instead of addition from a second array. `array_scale_safety_wit_2` should follow from the contract overflow guard instantiated at the current loop index. `array_scale_entail_wit_1` initializes the invariant with `l1 = nil` and `l2 = lo`. `array_scale_entail_wit_2` must show that replacing index `i_2` in `l1_2 ++ l2_2` with `la[i_2] * k_pre` can be represented as a new processed prefix `l1_2 ++ [la[i_2] * k_pre]` and the remaining suffix `sublist (i_2 + 1) n_pre lo`. `array_scale_return_wit_1` should use `i_3 = n_pre`, prove the suffix `l2` has zero length and is `nil`, then choose `lr = l1`.

I will first adapt the stable proof scripts from `examples/array_add/coq/generated/array_add_proof_manual.v`, changing the element expression from `la[i] + lb[i]` to `la[i] * k_pre` and removing the second input array. If compilation exposes a naming mismatch after `pre_process`, I will use the Coq error/proof state to revise only the failing lemma.

## 2026-04-19 23:40:45 +0800

The first full compile attempt failed before reaching the proof because I invoked `coqc` from `/home/yangfp/QualifiedCProgramming`; the `_CoqProject` load paths are usable from `/home/yangfp/QualifiedCProgramming/SeparationLogic`. Rerunning from the correct directory compiled `array_scale_goal.v` and `array_scale_proof_auto.v`, then failed in `array_scale_proof_manual.v` at line 101 with `Tactic failure: Cannot find witness`.

I inspected `array_scale_entail_wit_2` in `coqtop`. After the list rewrites and `entailer!`, the remaining pure goals are ordered as: suffix element relation, prefix element relation, suffix length, and prefix length. My first script put the prefix element proof in the first bullet, so Coq was trying to prove the suffix relation using the wrong `t < i_2 \/ t = i_2` split. I will reorder the bullets: first prove the suffix relation with `Znth_sublist`, then prove the prefix relation by splitting `t < i_2` versus `t = i_2`, then prove the two length goals.

The next compile reached `array_scale_return_wit_1` and failed because the return proof reused the `array_add` hypothesis numbering. In this generated goal, `H5` is `Zlength l2 = n_pre - i_3`, while `H6` is the processed-prefix semantic relation. I will change the nil-suffix proof to rewrite `H5`, and after substituting `i_3 = n_pre` I will use `H6` directly for the result-list element relation.
