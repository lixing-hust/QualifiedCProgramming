# Proof Reasoning

## Round 1

- Read `string_equal_goal.v`, `string_equal_proof_auto.v`, and `string_equal_goal_check.v`.
- The generated `proof_manual.v` contains eleven unfinished lemmas:
  - `proof_of_string_equal_entail_wit_2`
  - `proof_of_string_equal_entail_wit_3_1`
  - `proof_of_string_equal_entail_wit_3_2`
  - `proof_of_string_equal_entail_wit_4_1`
  - `proof_of_string_equal_entail_wit_4_2`
  - `proof_of_string_equal_return_wit_1`
  - `proof_of_string_equal_return_wit_2`
  - `proof_of_string_equal_return_wit_3`
  - `proof_of_string_equal_return_wit_4`
  - `proof_of_string_equal_return_wit_5`
  - `proof_of_string_equal_return_wit_6`
- Classification:
  - `entail_wit_2` is the loop-preservation step after reading equal nonzero characters
  - `entail_wit_3_*` and `entail_wit_4_*` are the loop-exit bridge goals that turn the first seen `0` into exact index equalities and then into `na = nb`
  - the `return_wit_*` goals are pure list/string-spec obligations over `string_equal_spec`
- Planned helper-lemma set:
  - `Znth` at the appended terminator
  - “nonzero implies index is before the logical end”
  - “first zero is at the logical end”
  - `string_equal_spec` equality, mismatch, and shorter-string cases
- Proof strategy:
  - keep witness scripts short with `pre_process`, `entailer!`, explicit length facts from `CharArray.full_length`, and calls into helper lemmas
  - compile immediately after importing the helper layer so the first stable failure is recorded against the current workspace rather than the older run

## Round 2

- First stable `coqc` failure in the current workspace:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: the first `Hlen_la` extraction inside `proof_of_string_equal_entail_wit_2`
  - error: `No matching clauses for match.`
- Diagnosis:
  - after `pre_process` and `prop_apply CharArray.full_length`, the produced length fact is not a direct `Zlength (...) = ...` hypothesis
  - the actual hypothesis shape is `Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1`
  - so the borrowed helper script was matching the wrong normalization form for this Coq environment
- Fix direction:
  - rewrite all length-extraction matches to target the observed `Z.of_nat (Datatypes.length ...)` shape first
  - convert them back through `Zlength_correct`
  - rerun the compile chain before changing any witness logic

## Round 3

- The next `coqc` failure stayed in `proof_of_string_equal_entail_wit_2`, but moved past the length facts.
- Stable error:
  - `This proof is focused, but cannot be unfocused this way`
  - location: the closing brace of the `Hi_lt_na` subproof
- Diagnosis:
  - the compact `eapply ...; eauto` script was leaving an unresolved side condition in this Coq build
  - the obligation is simple: instantiate `app_Znth_nonzero_lt` with the concrete list and feed it the already available bound and nonzero hypotheses
- Fix direction:
  - replace the `eauto`-driven calls with explicit `apply ... with (l := ...)` steps for both `Hi_lt_na` and `Hi_lt_nb`
  - rerun `coqc` before touching later witnesses

## Round 4

- The explicit `app_Znth_nonzero_lt` instantiations exposed a remaining direction error in the bound rewrite.
- Stable compile error:
  - the subgoal expected `i <= Zlength la` / `i <= Zlength lb`
  - but the script rewrote to the opposite direction and left Coq trying to compare `i <? na` against `i <? Zlength la`
- Fix direction:
  - change those two bound rewrites to `rewrite <- Hlen_la` and `rewrite <- Hlen_lb`
  - keep the rest of `entail_wit_2` unchanged for the next compile probe

## Round 5

- The bound-direction fix was still not enough because the assertion target itself remained `i < na` / `i < nb`, while `app_Znth_nonzero_lt` concludes `i < Zlength la` / `i < Zlength lb`.
- Stable compile error:
  - Coq still tried to unify the lemma conclusion directly with `i < na`
- Fix direction:
  - first derive `Hi_lt_la : i < Zlength la` and `Hi_lt_lb : i < Zlength lb`
  - then convert them to `i < na` and `i < nb` with `lia` using `Hlen_la` and `Hlen_lb`

## Round 6

- The nested `Hi_lt_la` / `Hi_lt_lb` helper shape was correct, but the bound rewrite inside those inner subgoals had to go in the opposite direction from the outer failed attempt.
- Stable compile error:
  - `Found no subterm matching "na" in the current goal`
  - location: the `i <= Zlength la` subgoal inside `Hi_lt_la`
- Diagnosis:
  - once the target is already in `Zlength` form, Coq needs `rewrite Hlen_la` and `rewrite Hlen_lb` to turn it into the available `i <= na` / `i <= nb` hypotheses
- Fix direction:
  - flip only those inner rewrites back to `rewrite Hlen_la` and `rewrite Hlen_lb`
  - keep the outer `lia` conversion intact

## Round 7

- After the setup fixes, the next stable failure was no longer about lengths or bounds; it was the tail of `proof_of_string_equal_entail_wit_2`.
- Stable compile error:
  - `No product even after head-reduction`
  - location: `intros j Hj0 Hjlt` after `entailer!`
- Diagnosis:
  - in the current generated witness shape, `entailer!` had already normalized away the outer product expected by that old manual script
  - so the borrowed explicit `forall` handling was no longer attached to the actual remaining goal structure
- Fix direction:
  - remove the obsolete `intros/destruct` tail and first test whether `entailer!` now closes `entail_wit_2` directly
  - only if a new residual goal appears should we inspect that exact proof state

## Round 8

- Re-read `string_equal_entail_wit_2` in `string_equal_goal.v` against the current proof body.
- Current blocker:
  - the theorem only needs three new pure facts beyond the preserved resources:
    - `i + 1 <= na`
    - `i + 1 <= nb`
    - extension of the prefix-equality fact from `< i` to `< i + 1`
  - the existing setup already derives `i < na` and `i < nb`, so the remaining open goal is consistent with `entailer!` leaving the strengthened `forall j < i + 1` obligation behind
- Planned repair:
  - keep the existing length extraction and bound derivations unchanged
  - after `entailer!`, explicitly prove the residual `forall` by splitting `j < i + 1` into `j < i` or `j = i`
  - use the old prefix hypothesis on the `< i` branch and the current-character equality hypothesis on the `j = i` branch

## Round 9

- Compile result after the explicit `forall` tail:
  - `proof_of_string_equal_entail_wit_2` now reaches the `j = i` branch
  - the remaining error is a shape mismatch between:
    - hypothesis `H : Znth i (la ++ 0 :: nil) 0 = Znth i (lb ++ 0 :: nil) 0`
    - target `Znth i la 0 = Znth i lb 0`
- Diagnosis:
  - because `i < na` and `i < nb` were already derived, this is not a semantic gap
  - the branch just needs to rewrite both sides of `H` from the appended arrays back to the base lists using `app_Znth1`
- Planned repair:
  - in the `j = i` branch, rewrite `H` with `app_Znth1` on both sides using `Hi_lt_na`, `Hi_lt_nb`, `Hlen_la`, and `Hlen_lb`
  - keep the rest of the witness unchanged

## Round 10

- After `entail_wit_2` normalized successfully, the first stable failure moved to `proof_of_string_equal_entail_wit_3_1`.
- Current blocker:
  - the script enters the left disjunct with `left; entailer!` before proving the memory-side equality `i = na`
  - the theorem target for that branch already contains `(&( "i" )) # Int |-> na`, so the bridge must establish the exact exit index first
- Diagnosis:
  - `first_zero_at_end` is already the right lemma, but its result must be used before opening the disjunct
  - the same structural issue is present symmetrically in `proof_of_string_equal_entail_wit_3_2`
- Planned repair:
  - in `entail_wit_3_1`, derive `Hi_eq_na : i = na`, `subst i`, then choose the left branch and finish with `entailer!`
  - in `entail_wit_3_2`, derive `Hi_eq_nb : i = nb`, `subst i`, then choose the right branch and finish with `entailer!`

## Round 11

- The direct `coqtop` inspection of `entail_wit_3_1` showed the exact remaining subgoal after `subst i; left; entailer!`:
  - the branch-local `forall j, 0 <= j < na -> Znth j la 0 = Znth j lb 0`
- Diagnosis:
  - the current prefix hypothesis is still present as `H6 : forall j_2, 0 <= j_2 < na -> ...`
  - so the branch is not blocked on separation logic anymore, only on explicitly reusing that preserved prefix fact
  - the same post-`entailer!` shape should appear in the symmetric `entail_wit_3_2`
- Planned repair:
  - append `intros j Hj0 Hjlt; apply H6; lia` after `entailer!` in both bridge lemmas
  - recompile before touching later witnesses

## Round 12

- The conditional tail still left `proof_of_string_equal_entail_wit_3_1` with open goals at `Qed`.
- Diagnosis:
  - the problematic part is not the core math anymore but the exact proof-state packaging produced by `pre_process` for these two disjunctive bridge witnesses
  - there is already a previously verified `string_equal` workspace whose `entail_wit_3_1` / `entail_wit_3_2` scripts are structurally identical and use the more explicit `unfold ...; intros ...; Intros.` style
- Planned repair:
  - replace only `entail_wit_3_1` and `entail_wit_3_2` with that explicit proven shape
  - preserve the current workspace’s length-pattern adaptation (`Z.of_nat (Datatypes.length ...)`)

## Round 13

- Recompiled the current workspace with the full compile chain to get a non-stale blocker.
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: the sepcon normalization in `proof_of_string_equal_entail_wit_3_1`
  - error: `Found no subterm matching ...` for the `logic_equiv_sepcon_assoc` rewrite
- Diagnosis:
  - the current goal’s left-hand heap is already packaged as `CharArray.full b_pre ... ** (CharArray.full a_pre ... ** &( "i" ) # Int |-> i)` after `pre_process`
  - so the imported assoc/comm rewrite is targeting the wrong concrete sepcon shape in this environment
  - the bridge is still expected to be purely structural, so the right next probe is to remove only those brittle heap rewrites and let `entailer!` consume the existing heap shape directly
- Planned repair:
  - delete the `logic_equiv_sepcon_assoc` / `logic_equiv_sepcon_comm` rewrites from `entail_wit_3_1` and `entail_wit_3_2`
  - keep the `first_zero_at_end` bridge and branch-local prefix proof unchanged
  - recompile immediately to see whether the blocker moves to a residual pure goal or closes cleanly

## Round 14

- Compile result after removing the brittle entailment-level sepcon rewrites:
  - `proof_of_string_equal_entail_wit_3_1` still ends with `Attempt to save an incomplete proof`
- Exact proof-state probe:
  - after `subst i; left; entailer!`, the branch no longer fails on the heap rewrite
  - instead it reduces to a single model-level goal whose heap payload is already concrete
  - the remaining shape is not a new arithmetic/string fact; it is the final packaging of the branch conjunction together with the reordered heap chunk
- Planned repair:
  - first try a second `entailer!` on that reduced branch goal before adding any new structural rewrites
  - if that still leaves a heap-ordering residue, normalize only the final branch heap shape at the model level

## Round 15

- Result of the second-`entailer!` probe:
  - `proof_of_string_equal_entail_wit_3_1` still ends with open goals
- More precise diagnosis from the model-level residual:
  - after `subst i`, the remaining branch proof already has all pure facts in context and one heap witness of the form
    - `CharArray.full b_pre ... ** (CharArray.full a_pre ... ** &( "i" ) # Int |-> na)`
  - the target branch heap is
    - `&( "i" ) # Int |-> na ** (CharArray.full a_pre ... ** CharArray.full b_pre ...)`
  - so the last missing step is just a three-factor sepcon reordering on that explicit witness, not another logical derivation
- Planned repair:
  - replace the extra `entailer!` in `entail_wit_3_1` with an explicit local `assert` that rewrites the target heap into the witness order and then closes with `exact`
  - recompile to confirm whether `entail_wit_3_2` needs the same treatment

## Round 16

- The generic `match goal` version of the local heap-transport failed immediately with:
  - `No matching clauses for match.`
- Diagnosis:
  - the residual branch context shape is stable enough in interactive inspection to expose a concrete heap witness name (`H15`), but the generic pattern was still too optimistic about the post-`entailer!` proof state packaging
- Planned repair:
  - inline the same three-rewrite heap transport using the concrete residual witness name from the current generated proof state
  - recompile and only generalize further if that naming assumption breaks in a later blocker

## Round 17

- The concrete-witness transport failed on the first rewrite with:

## Round 18

- Re-checked the current blocker with direct `coqtop` inspection against the generated `string_equal_goal.v`.
- Stable finding:
  - `Goal string_equal_entail_wit_3_1.` followed by `unfold string_equal_entail_wit_3_1.` does expose the expected outer `forall ... |-- ...` shape in isolation
  - so the latest `coqc` error at line 367 (`No product even after head-reduction.`) is not a semantic contradiction in the witness statement itself
- Diagnosis:
  - the blocker is the proof entry shape inside `string_equal_proof_manual.v`
  - in this workspace and Coq environment, the explicit `unfold ...; intros ...; Intros.` pattern for `entail_wit_3_1` / `entail_wit_3_2` is less stable than the generated-goal-native `pre_process` entry used by the other witnesses
  - the downstream proof body still matches the current theorem: derive `i = na` / `i = nb`, choose the corresponding disjunct, and discharge the preserved prefix fact
- Planned repair:
  - replace only the opening of `proof_of_string_equal_entail_wit_3_1` and `proof_of_string_equal_entail_wit_3_2` with `pre_process`
  - keep the length extraction, `first_zero_at_end` bridge, branch choice, and final prefix proof unchanged
  - recompile immediately to see whether the blocker clears or moves forward to the next witness

## Round 19

- Compile result after the `pre_process` entry repair:
  - `coqc` now gets through the theorem head and the `first_zero_at_end` bridge
  - the new first stable failure is line 384, exactly at the leftover `intros j ...` tail after `left; entailer!`
- Exact proof-state finding:
  - after `subst i; left; entailer!`, the goal is no longer a top-level `forall`
  - it has become a model-level packaged conjunction for the chosen disjunct, with a concrete heap witness already present in context
  - so the old `intros` tail is structurally stale in this environment
- Retrieved proof pattern:
  - `CAV/examples/string_is_empty/coq/generated/string_is_empty_proof_manual.v` finishes the analogous disjunctive packaging step with:
    - `left.`
    - `entailer!.`
    - `simpl.`
    - `repeat split; auto; lia.`
- Planned repair:
  - replace the stale `intros/apply Hpref` tails in `entail_wit_3_1` and `entail_wit_3_2` with the same `simpl; repeat split; auto; lia` packaging pattern
  - recompile immediately to see whether the branch closes or whether a remaining heap-order side condition still needs one explicit rewrite

## Round 20

- Compile result after the `simpl; repeat split; auto; lia` packaging probe:
  - the branch no longer fails on the stale `forall` shape
  - the new stable error is `Cannot find witness.` at the final split line of `proof_of_string_equal_entail_wit_3_1`

## Round 21

- Re-read the latest `logs/compile_proof_manual.log` instead of relying on the older retry notes.
- Current first stable compile error:
  - file: `output/verify_20260419_003208_string_equal/coq/generated/string_equal_proof_manual.v`
  - line: 516
  - error: `The relation derivable1 is not a declared symmetric relation.`
- Diagnosis:
  - the active blocker has moved past the older `entail_wit_3_1` packaging work
  - the failing command is the bare `symmetry.` at the start of `proof_of_string_equal_return_wit_1`
  - after `pre_process`, these return witnesses are proving an entailment whose pure payload is `0 = string_equal_spec ...` or `1 = string_equal_spec ...`
  - `symmetry.` tries to flip the outer entailment relation `derivable1`, not just the inner pure equality, so Coq rejects it before reaching the intended helper lemma
- Planned repair:
  - remove the invalid `symmetry.` uses from the return witnesses
  - prove the needed spec fact in its native helper-lemma orientation (`string_equal_spec ... = 0` / `= 1`)
  - then rewrite the pure target equality explicitly inside each witness
  - recompile `proof_manual.v` immediately to see which witness becomes the next blocker

## Round 22

- Compile result after removing the invalid entailment-level `symmetry.` in the return witnesses:
  - the first failure moved to `proof_of_string_equal_return_wit_2`
  - location: line 603
  - error: `Cannot find witness.`
- Diagnosis:
  - this is not a missing semantic fact about string equality
  - the failure is the local `match goal with Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ => ... end` used to extract lengths
  - `return_wit_2` does not actually need any `CharArray.full_length` bridge; the theorem already gives `nb = na` plus the full prefix-equality fact up to `nb`
  - so the current length-extraction block is unnecessary proof-state coupling and should be removed instead of repaired
- Planned repair:
  - replace `proof_of_string_equal_return_wit_2` with the direct `string_equal_spec_equal` proof shape
  - use the existing equality hypothesis for lengths and the existing prefix hypothesis unchanged
  - recompile to expose the next blocker, if any

## Round 23

- `coqtop` check on `Goal string_equal_return_wit_2` showed the earlier simplification was too aggressive.
- Observed proof state:
  - after `pre_process`, the theorem has only pure hypotheses `nb = na`, nonzero-prefix facts, and the prefix-equality fact
  - the needed `Zlength la = na` / `Zlength lb = nb` facts still come from `CharArray.full_length`
  - after `prop_apply (CharArray.full_length ...)` and `Intros.`, the current environment exposes:
    - `H3 : Z.of_nat (length (la ++ 0 :: nil)) = na + 1`
    - and symmetrically for `lb`
- Diagnosis:
  - the failed `lia` at line 603 was not the right place to simplify; the missing step is to recover `Zlength la = na` and `Zlength lb = nb` from the heap lengths before calling `string_equal_spec_equal`
- Planned repair:
  - restore the two `CharArray.full_length` applications in `return_wit_2`
  - convert their `Z.of_nat (length (...)) = ...` outputs back to `Zlength` equalities with `Zlength_correct`, `Zlength_app`, `Zlength_cons`, and `Zlength_nil`
  - keep the final equality proof short once those two length facts are available

## Round 24

- Compile result after restoring the heap-length bridge in `return_wit_2`:
  - the theorem now gets through the `Zlength` obligations
  - the new first failure is in the final prefix-reuse line
  - exact error: the constructed proof term has type `0 <= j < na`, while the preserved prefix hypothesis expects `0 <= j < nb`
- Diagnosis:
  - this is only a branch-local index-range conversion using the existing hypothesis `H : nb = na`
  - no new list reasoning is needed
- Planned repair:
  - rewrite the bound side with `H` before applying the preserved prefix fact in `return_wit_2`
  - recompile immediately to expose the next blocker

## Round 25

- The first bound-conversion attempt in `return_wit_2` used the wrong rewrite direction.
- Stable compile error:
  - `Found no subterm matching "nb" in Hjlt.`
- Diagnosis:
  - after `rewrite Hlen_la in Hjlt`, the local fact is `Hjlt : j < na`
  - the target hypothesis expects `j < nb`
  - since `H : nb = na`, the required conversion is `rewrite <- H in Hjlt`, not `rewrite H in Hjlt`
- Planned repair:
  - flip that one rewrite direction and rerun the compile chain

## Round 26

- Compile result after fixing the rewrite direction in `return_wit_2`:
  - `return_wit_2` now passes
  - the first failure moved to `proof_of_string_equal_return_wit_3`
  - current error shows the second argument of `string_equal_spec_zero_nonzero` is being filled with `H1 : Znth nb (la ++ 0 :: nil) 0 = 0`, while the lemma actually expects a bound of shape `nb <= Zlength la`
- Diagnosis:
  - `return_wit_3` still needs the same heap-length bridge as `return_wit_2`
  - after `entailer!`, the theorem only has pure index/break facts; the required `Zlength la = na` and `Zlength lb = nb` must again come from `CharArray.full_length`
- Planned repair:
  - add the two `CharArray.full_length` steps back to `return_wit_3`
  - derive `Hlen_la` / `Hlen_lb`
  - feed `string_equal_spec_zero_nonzero` the arguments in the correct order using those bounds

## Round 27

- Compile result after restoring the length bridge in `return_wit_3`:
  - the theorem now reaches the final helper-lemma argument
  - the new failure is a hypothesis-shape mismatch:
    - available: `forall j, 0 <= j < nb -> ...`
    - required by `string_equal_spec_zero_nonzero`: `forall j, 0 <= j -> j < nb -> ...`
- Diagnosis:
  - this is only a currying/packaging mismatch in the preserved prefix fact
  - the semantic content is already present in `H8`
- Planned repair:
  - wrap `H8` with `intros j Hj0 Hjlt; apply H8; lia`
  - recompile to expose the next witness

## Round 28

- Compile result after fixing the curried prefix argument in `return_wit_3`:
  - `return_wit_3` now passes
  - the first failure moved to `proof_of_string_equal_return_wit_4`
  - current error shows the same pattern as the previous theorem, but on the symmetric branch:
    - the proof is providing `H2 : 0 <= nb + 1` where the helper lemma expects a bound of shape `na <= Zlength lb`
- Diagnosis:
  - `return_wit_4` also needs `CharArray.full_length` on both arrays before calling `string_equal_spec_zero_nonzero`
  - the only extra detail is that the theorem proves the symmetric call `string_equal_spec lb la = 0`, so the preserved prefix equality must still be flipped pointwise
- Planned repair:
  - add the same `Hlen_la` / `Hlen_lb` bridge used in `return_wit_3`
  - feed the symmetric bound/order arguments to `string_equal_spec_zero_nonzero`
  - keep the final prefix proof as `symmetry; apply H8; lia`

## Round 29

- Compile result after repairing `return_wit_4`:
  - `return_wit_4` now passes
  - the first failure moved to `proof_of_string_equal_return_wit_5`
- Diagnosis split:
  - `return_wit_5` is not another ordinary zero/nonzero branch
  - once `CharArray.full_length` gives `Zlength la = na`, the hypothesis `Znth na (la ++ 0 :: nil) 0 <> 0` contradicts `Znth_app_zero`
  - so `return_wit_5` should close by contradiction rather than by another spec helper call
  - `return_wit_6` is the real symmetric stop case at index `nb`: `la[nb]` is nonzero while `lb[nb]` is the terminator, so it should use the symmetric `string_equal_spec_zero_nonzero` pattern with the same length bridge
- Planned repair:
  - rewrite `return_wit_5` into a contradiction proof using `Hlen_la` and `Znth_app_zero`
  - rewrite `return_wit_6` to derive `string_equal_spec lb la = 0` from `nb = Zlength lb`, then finish with `string_equal_spec_sym`

## Round 21

- Re-read the actual current `string_equal_proof_manual.v` in this workspace instead of relying on the previous reasoning trail.
- Stable compile blocker from `logs/compile_proof_manual.log`:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 383 inside `proof_of_string_equal_entail_wit_3_1`
  - error: `Found no subterm matching ...`
- Diagnosis:
  - the file still contains the older `logic_equiv_sepcon_comm` / `logic_equiv_sepcon_assoc` rewrites that were already identified as brittle for this generated heap shape
  - so the current blocker is earlier than the later `Cannot find witness` probe recorded above
- Planned repair:
  - remove only those explicit sepcon rewrites from `entail_wit_3_1` and `entail_wit_3_2`
  - keep the `pre_process` entry, `first_zero_at_end` bridge, branch choice, and `simpl; repeat split; auto; try lia` packaging
  - recompile immediately to get the next real blocker from the same workspace state

## Round 22

- After removing the stale goal-level rewrites, `coqc` reached the real remaining obligation in `proof_of_string_equal_entail_wit_3_1`:
  - `Attempt to save an incomplete proof`
- `coqtop` inspection showed the exact post-`left; entailer!; simpl; repeat split; auto; try lia` state:
  - all pure side conditions are already solved
  - the only remaining goal is the model-level heap atom
    - target: `(&( "i" ) # Int |-> na ** (CharArray.full a_pre ... ** CharArray.full b_pre ...)) m`
    - witness in context: `H15 : (CharArray.full b_pre ... ** (CharArray.full a_pre ... ** &( "i" ) # Int |-> na)) m`
- Reusable proof pattern:
  - prove a small local entailment that rewrites `b ** (a ** i)` into `i ** (a ** b)` using exactly three sepcon rewrites:
    - `logic_equiv_sepcon_assoc`
    - outer `logic_equiv_sepcon_comm`
    - inner `logic_equiv_sepcon_comm`
  - then apply that entailment to the current model witness
- Planned repair:
  - add the local heap-reordering entailment in both `entail_wit_3_1` and the symmetric `entail_wit_3_2`
  - keep all arithmetic and prefix-equality steps unchanged

## Round 23

- Compile result after adding the local heap entailments:
  - `proof_of_string_equal_entail_wit_3_1` is no longer the blocker
  - the next failure is in `proof_of_string_equal_entail_wit_3_2`
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 453
  - symptom: `H15` is being used as if it were the heap witness, but in this theorem `H15` is the length fact for `la`
- Diagnosis:
  - the local heap entailment itself is correct
  - only the final application target is wrong because the post-`entailer!` witness numbering differs between the two symmetric lemmas
  - in `entail_wit_3_2`, the actual heap witness is `H17`
- Planned repair:
  - change only the final `exact (Hheap _ H15)` in `entail_wit_3_2` to use `H17`
  - recompile the full chain again

## Round 24

- Compile result after fixing the heap-witness numbering:
  - the next blocker moved to `proof_of_string_equal_entail_wit_4_1`
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 472
  - symptom: `first_zero_at_end` expects a length fact for the list whose index-`na` element is known to be zero, but the script supplies `Hlen_la : Zlength la = na`
- Diagnosis:
  - `entail_wit_4_1` proves `nb = na` from `Znth na (lb ++ 0 :: nil) 0 = 0`, so it must use the `lb` length fact and the `lb` nonzero-prefix hypothesis
  - symmetrically, `entail_wit_4_2` proves `na = nb` from `Znth nb (la ++ 0 :: nil) 0 = 0`, so it must use the `la` length fact instead of the current `lb` one
  - the two bridge lemmas currently have those length extractions swapped
- Planned repair:
  - in `entail_wit_4_1`, extract `Hlen_lb` from `CharArray.full_length b_pre ...` and feed `first_zero_at_end` with the `lb` facts
  - in `entail_wit_4_2`, extract `Hlen_la` from `CharArray.full_length a_pre ...` and feed `first_zero_at_end` with the `la` facts
  - keep the rest of both witnesses unchanged

## Round 25

- Compile result after swapping the two length facts:
  - the theorem selection is now correct, but `first_zero_at_end` still rejects the nonzero-prefix hypothesis in `entail_wit_4_1`
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 473
  - symptom: `H7` has shape `forall k, 0 <= k < nb -> ...`, while `first_zero_at_end` expects the curried shape `forall k, 0 <= k -> k < nb -> ...`
- Diagnosis:
  - this is only a binder-shape mismatch; the content is already sufficient
  - the symmetric `entail_wit_4_2` uses the same packed `<` hypothesis shape and needs the same adaptation
- Planned repair:
  - wrap the packed hypotheses as `intros k Hk0 Hklt; apply H7; lia` and `intros k Hk0 Hklt; apply H6; lia`
  - leave the rest of both bridge lemmas unchanged

## Round 26

- `coqtop` inspection of `entail_wit_4_1` after `subst nb; entailer!` showed that the theorem is no longer blocked on the zero-at-end bridge itself.
- Exact remaining obligations:
  - transport the points-to atom from `na` to `Zlength lb`
  - extend the preserved prefix-equality fact from `< na` to `< Zlength lb`
- Key context after substitution:
  - `Hnb_eq_na : Zlength lb = na`
  - preserved prefix fact `H8 : forall j, 0 <= j < na -> Znth j la 0 = Znth j lb 0`
- Planned repair:
  - after `entailer!` in `entail_wit_4_1`, add two explicit tail obligations:
  - `rewrite <- Hnb_eq_na; entailer!`
  - discharge the remaining two `forall` goals by rewriting the bound with `Hnb_eq_na` and reusing `H6` / `H8`
  - recompile to see whether the symmetric `entail_wit_4_2` needs a similar explicit tail

## Round 27

- The compile chain has moved past the earlier bridge blockers into the return witnesses.
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 516
  - symptom: bare `symmetry.` is being applied while the goal is still an entailment (`derivable1`) rather than a pure equality
- Diagnosis:
  - the return witnesses preserved the old script shape `pre_process; symmetry; ...`
  - in this environment, they need the same normalization pattern already used in other examples:
    - `pre_process`
    - `entailer!`
    - then prove the pure equality
- Planned repair:
  - add `entailer!` before the equality reasoning in the return witnesses, starting with `return_wit_1` and propagating the same fix to the analogous `return_wit_2`-`return_wit_6` scripts

## Round 28

- After normalizing the return witnesses with `entailer!`, the next blocker is no longer the entailment/equality mismatch.
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 519 in `return_wit_1`
  - symptom: the first premise passed to `string_equal_spec_mismatch` is `H0`, but after `entailer!` that hypothesis is `Znth i (lb ++ 0 :: nil) 0 <> 0`, not the required bound `0 <= i`
- Diagnosis:
  - the old proof was relying on pre-`entailer!` hypothesis numbering
  - in the normalized state, the relevant facts are:
    - `H4 : 0 <= i`
    - `H5 : i <= na`
    - `H6 : i <= nb`
    - `H2 : Znth i (la ++ 0 :: nil) 0 <> 0`
    - `H0 : Znth i (lb ++ 0 :: nil) 0 <> 0`
    - `H9 : forall j, 0 <= j < i -> ...`
- Planned repair:
  - rewrite `return_wit_1` to pass those facts explicitly instead of using `eauto` / old numbers
  - recompile to expose the next normalized return-witness mismatch

## Round 29

- `return_wit_1` now compiles, and the next failure is `return_wit_2`.
- Stable compile error:
  - file: `coq/generated/string_equal_proof_manual.v`
  - line: 597
  - symptom: the script still calls `string_equal_spec_mismatch`, which concludes `= 0`, while this witness needs the success case `1 = string_equal_spec la lb`
- Diagnosis:
  - `return_wit_2` is the “all characters matched and both strings end together” branch
  - so it must use `string_equal_spec_equal`, not the mismatch lemma
  - just like `return_wit_1`, it also needs explicit length facts extracted from `CharArray.full_length` before `entailer!`
- Planned repair:
  - rebuild `return_wit_2` with `Hlen_la` / `Hlen_lb`
  - prove the length equality using the branch fact `nb = na`
  - reuse the preserved prefix-equality hypothesis for the extensional equality premise
- Diagnosis:
  - the pure parts of the chosen disjunct are handled
  - the remaining subgoal is the heap payload in target order
  - the available branch witness still has the source order `b ** (a ** i)` while the target expects `i ** (a ** b)`
- Planned repair:
  - keep the `simpl; repeat split; auto; lia` pure packaging
  - add one explicit local heap transport that rewrites the concrete branch witness through:
    - swap `a` and `i`
    - reassociate
    - swap `b` and `i`
    - reassociate back
    - swap `b` and `a`
  - first apply that transport in `entail_wit_3_1`; if compilation then moves symmetrically to `entail_wit_3_2`, apply the same pattern there

## Round 21

- Compile result after the generic local heap-transport attempt:
  - the proof no longer fails on the transport rewrites themselves
  - the new stable error is `No matching clauses for match.` at the `match goal` wrapper
- Diagnosis:
  - the compiled branch proof state does contain the concrete heap witness seen in interactive inspection
  - but the generic `_ ** (_ ** _)` pattern is still too weakly shaped to match the exact compiled context here
- Planned repair:
  - replace the generic `match goal` wrapper with the concrete residual witness name observed during the interactive probe (`H15`)
  - keep the transport rewrites themselves unchanged so only the witness capture mechanism changes

## Round 22

- Compile result after switching to the concrete residual witness:
  - the branch still stops in the same local transport area
  - the new stable error is a `setoid rewrite failed` message on the first `rewrite ... in Hheap'`
- Diagnosis:
  - the transport order is still the right one
  - but rewriting inside the heap hypothesis introduces unresolved `Proper` side conditions in this SL library
- Planned repair:
  - perform the same sepcon comm/assoc rewrites on the goal instead of inside the hypothesis
  - then close the branch with the original concrete witness directly (`exact H15`)

## Round 23

- Compile result after moving the transport rewrites onto the goal:
  - the branch still fails in the local heap-transport block
  - the new stable error is `Found no subterm matching "CharArray.full b_pre ... ** CharArray.full a_pre ..."` on the first commutativity rewrite
- Diagnosis:
  - the goal-side transport sequence was applied in the wrong direction
  - the actual target heap still starts from the branch order `i ** (a ** b)`, so the first available inner sepcon is `a ** b`, not `b ** a`
- Planned repair:
  - keep the same five-step transport plan, but orient the goal rewrites from the actual current target:
    - swap `a` and `b`
    - reassociate to expose `i ** b`
    - swap `i` and `b`
    - reassociate to expose `i ** a`
    - swap `i` and `a`
  - then reuse `exact H15`

## Round 24

- Compile result after correcting the rewrite directions:
  - the heap transport is still blocked, now by `setoid rewrite failed` on the first goal-side commutativity step
- Diagnosis:
  - the same sepcon equalities are accepted in repository examples when they are applied at the entailment level before the goal is simplified down to a model-level proposition
  - once the branch has been reduced to a model-level goal, the library starts demanding extra `Proper` instances for these rewrites
- Planned repair:
  - move the sepcon comm/assoc normalization back before `entailer!`
  - normalize the chosen branch heap while the goal is still an entailment
  - then let `entailer!` and the existing `simpl; repeat split; auto; lia` finish the pure packaging
  - `Found no subterm matching "&( \"i\") # Int |-> na ** CharArray.full ... ** CharArray.full ..."`
- Diagnosis:
  - that message means the local heap target is still in the right-associated form `i ** (a ** b)`, while the attempted `rewrite <- logic_equiv_sepcon_assoc` was searching for the left-associated shape
- Planned repair:
  - flip only that first rewrite to the forward direction `rewrite (logic_equiv_sepcon_assoc ...)`
  - keep the two commutativity rewrites and the concrete witness unchanged

## Round 18

- The forward associativity attempt failed with:
  - `Tactic failure: Nothing to rewrite.`
- Diagnosis:
  - at the point where `Hheap_target` is proved, the branch heap target is apparently already left-associated enough that the assoc rewrite is irrelevant
  - the remaining gap is therefore just the two commutativity steps needed to move `&( "i" ) # Int |-> na` behind `CharArray.full a_pre ...` and then move the resulting chunk behind `CharArray.full b_pre ...`
- Planned repair:
  - remove the assoc rewrite from `Hheap_target`
  - keep only the two comm rewrites before `exact H15`

## Round 19

- Retrieved the previously verified workspace:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_183752_string_equal/coq/generated/string_equal_proof_manual.v`
- Reusable proof pattern found there:
  - `proof_of_string_equal_entail_wit_3_1` and `3_2` are stable when written in the explicit
    - `unfold ...; intros ...; Intros.`
    shape
  - after proving `i = na` / `i = nb`, that version closes with just `left/right; entailer!; intros ...; apply Hpref; lia`
- Diagnosis:
  - the fragile part in the current workspace is not the semantic bridge itself but the `pre_process`-packaged heap state
  - the older explicit witness shape avoids that packaging mismatch altogether
- Planned repair:
  - replace only `entail_wit_3_1` and `entail_wit_3_2` with the older explicit proof skeleton
  - adapt only the `CharArray.full_length` extraction to the current `Z.of_nat (Datatypes.length ...)` form
