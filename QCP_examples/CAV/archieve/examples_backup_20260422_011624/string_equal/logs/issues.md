# Verify Issues

## Issue 1: workspace-local doc bundle was missing

- Phenomenon:
  - the requested workspace only contained `original/` and `logs/`, so the skill-mandated paths like `doc/SCOPE.md`, `doc/PERMISSIONS.md`, `doc/experiences/README.md`, and `doc/retrieval/INDEX.md` were absent inside the workspace
- Trigger:
  - this workspace was initialized without the usual copied `doc/` subtree
- Localization:
  - `output/verify_20260419_003208_string_equal/`
- Fix:
  - read the repository-level `doc/` files instead
  - used the repository-level `doc/retrieval/INDEX.md` controlled vocabulary to backfill `logs/workspace_fingerprint.json`
- Result:
  - the workflow could continue without violating the controlled-vocabulary requirement for `semantic_description` and `keywords`

## Issue 2: `string_equal` needed explicit Verify annotations before symbolic execution

- Phenomenon:
  - the active annotated C file initially matched the input contract but had no loop invariant, no loop-exit assertion, and no branch-local assertion
- Trigger:
  - `string_equal` compares two null-terminated strings with a `while (1)` loop and early exits on mismatch or terminator, so the generated VC needs preserved shared-prefix semantics and exit-state facts
- Localization:
  - `annotated/verify_20260419_003208_string_equal.c`
- Fix:
  - added a loop invariant with:
    - bounds `0 <= i <= na` and `0 <= i <= nb`
    - parameter stability `a == a@pre`, `b == b@pre`
    - both preserved nonzero-prefix contract facts
    - the shared-prefix equality fact `(forall j < i, Znth(j, la, 0) == Znth(j, lb, 0))`
    - both `CharArray::full` resources
  - added a post-loop `Assert` with the pure exit consequence `i == na || i == nb`
  - added a branch-local `Assert` before `return 1` with `i == na && i == nb`
- Result:
  - `symexec` succeeded and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`

## Issue 3: the imported helper proof script assumed the wrong `CharArray.full_length` hypothesis shape

- Phenomenon:
  - the first `coqc` pass on the imported manual proof failed with:
    - `No matching clauses for match.`
- Trigger:
  - the borrowed helper layer expected `CharArray.full_length` to yield a direct `Zlength (...) = ...` hypothesis
  - in this workspace and Coq environment, the observed hypothesis shape was `Z.of_nat (Datatypes.length (...)) = ...`
- Localization:
  - `coq/generated/string_equal_proof_manual.v`
  - first failure inside `proof_of_string_equal_entail_wit_2`
- Fix:
  - rewrote all length-extraction matches to target the observed `Z.of_nat (Datatypes.length (...)) = ...` form
  - converted them back through `Zlength_correct`
- Result:
  - compilation moved past the length-extraction stage

## Issue 4: `proof_of_string_equal_entail_wit_2` still has unresolved residual goals

- Phenomenon:
  - after several focused proof-script repairs, `coqc` still fails in:
    - `proof_of_string_equal_entail_wit_2`
  - latest stable error:
    - `Attempt to save an incomplete proof (there are remaining open goals).`
- Trigger:
  - the older witness script shape does not line up cleanly with the current residual goals after `pre_process` and `entailer!`
  - part of the older tail (`intros j ...`) is obsolete for the current goal shape, but removing it leaves unfinished subgoals
- Localization:
  - `coq/generated/string_equal_proof_manual.v`
  - `logs/compile_proof_manual.log`
- Fix attempts:
  - normalized the length-fact extraction to the current `CharArray.full_length` output
  - replaced unstable `eauto` uses with explicit bound derivations
  - corrected several rewrite directions while deriving `i < na` and `i < nb`
  - removed the obsolete `intros j ...` tail once it no longer matched the proof state
- Result:
  - `proof_manual.v` no longer contains `Admitted.`
  - but `proof_manual.v` still does not compile, so `goal_check.v` was not compiled successfully

## Final state

- `symexec` succeeded on the current annotated file.
- `original/string_equal.v`, `string_equal_goal.v`, and `string_equal_proof_auto.v` compiled successfully.
- `string_equal_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`, but it still fails to compile in `proof_of_string_equal_entail_wit_2`.
- `goal_check.v` was not compiled because `proof_manual.v` did not finish.
- Non-`.v` files under `coq/` were deleted during cleanup.

## Issue 5: retry round cleared `entail_wit_2` but exposed a branch-packaging blocker in `entail_wit_3_1`

- Phenomenon:
  - the retry round repaired `proof_of_string_equal_entail_wit_2` enough to move compilation forward
  - the first stable failure then moved into `proof_of_string_equal_entail_wit_3_1`
  - the latest error after several bridge-proof rewrites is still an incomplete proof at `Qed`, with the branch proof stuck on packaging the chosen left disjunct rather than on the underlying arithmetic/string fact
- Trigger:
  - `first_zero_at_end` successfully derives `i = na`, but in this workspace’s current proof state the post-`left` branch does not line up cleanly with the older verified script shape
  - attempts to reuse the older `string_equal` proof pattern hit two environment-specific mismatches:
    - explicit `unfold ...; intros ...` failed with `No product even after head-reduction`
    - later heap-shape rewrites failed with `Found no subterm matching ... in the current goal`
- Localization:
  - `output/verify_20260419_003208_string_equal/coq/generated/string_equal_proof_manual.v`
  - current blocking lemma: `proof_of_string_equal_entail_wit_3_1`
- Fix attempts:
  - completed the residual `forall j < i + 1` proof in `proof_of_string_equal_entail_wit_2`
  - normalized the `j = i` branch by rewriting `Znth i (l ++ [0])` back to `Znth i l`
  - changed `entail_wit_3_1` / `entail_wit_3_2` to derive `i = na` / `i = nb` before choosing a branch
  - compared against the older verified `string_equal` workspace and tried both the explicit `unfold/intros/Intros` style and the `pre_process` style with both `CharArray.full_length` facts
  - tried branch-local sep-shape normalization with `logic_equiv_sepcon_assoc` / `logic_equiv_sepcon_comm`
- Result:
  - `proof_of_string_equal_entail_wit_2` is no longer the blocker
  - the active blocker is now the left-branch packaging of `proof_of_string_equal_entail_wit_3_1`
  - `proof_manual.v` still does not compile, so `goal_check.v` is still not compiled successfully

## Issue 6: the old verified `string_equal` witness shape still mismatches this workspace’s generated theorem packaging

- Phenomenon:
  - after several local repairs around `proof_of_string_equal_entail_wit_3_1`, the retry round compared against the previously verified workspace `verify_20260418_183752_string_equal`
  - copying back the older explicit proof shape for `entail_wit_3_1` / `entail_wit_3_2` did not resolve the blocker here
  - the latest stable compile error is:
    - `No product even after head-reduction.`
- Trigger:
  - in the older workspace, `unfold string_equal_entail_wit_3_1; intros ...; Intros.` worked directly
  - in the current workspace, the same explicit witness shape still does not match the generated theorem head after the earlier `Z.of_nat (Datatypes.length ...)` adaptation
- Localization:
  - `output/verify_20260419_003208_string_equal/coq/generated/string_equal_proof_manual.v`
  - latest stable failure at `proof_of_string_equal_entail_wit_3_1`, line 367 in the current file
- Fix attempts:
  - removed stale entailment-level sepcon rewrites that no longer matched the current `pre_process` heap shape
  - probed the exact post-`entailer!` model-level residual and tried local heap reordering
  - compared against the previously verified `string_equal` workspace and replaced `entail_wit_3_1` / `entail_wit_3_2` with the older explicit `unfold/intros/Intros` structure adapted to the current length-hypothesis form
- Result:
  - the workspace now has a newer, accurately logged blocker
  - but `proof_manual.v` still fails at `proof_of_string_equal_entail_wit_3_1`
  - `goal_check.v` remains uncompiled in this retry round

## Final state after retry round

- `workspace_fingerprint.json` remained valid and did not need further backfill.
- The active annotated C file was preserved unchanged in this retry round.
- The latest stable manual-proof blocker is:
  - theorem: `proof_of_string_equal_entail_wit_3_1`
  - error: `No product even after head-reduction.`
- `goal.v` and `proof_auto.v` compile, but `proof_manual.v` still does not.
- Non-`.v` files under `coq/` were deleted again after the failed compile probe.

## Issue 7: the active blocker is now entailment-level heap reordering inside `proof_of_string_equal_entail_wit_3_1`

- Phenomenon:
  - the retry continued past the old theorem-head mismatch and into the branch proof of `proof_of_string_equal_entail_wit_3_1`
  - the current stable failure is now:
    - `Found no subterm matching "CharArray.full a_pre ... ** &( \"i\" ) # Int |-> na" in the current goal.`
- Trigger:
  - after deriving `i = na` and choosing the left disjunct, the remaining work is only to normalize the branch heap from the source order to the target order before `entailer!`
  - several variants of the same normalization were tried:
    - post-`entailer!` `intros` tail from the older workspace
    - `simpl; repeat split; auto; lia`
    - local heap transport through a copied witness
    - goal-side sepcon comm/assoc rewrites after simplification
    - entailment-level sepcon comm/assoc rewrites before `entailer!`
  - the current entailment-level rewrite still does not match the concrete proof-state subterm in this workspace
- Localization:
  - `output/verify_20260419_003208_string_equal/coq/generated/string_equal_proof_manual.v`
  - current first failing line: the first entailment-level sepcon rewrite in `proof_of_string_equal_entail_wit_3_1`
  - current error recorded in `logs/compile_proof_manual.log`
- Fix attempts:
  - switched `entail_wit_3_1` / `entail_wit_3_2` from `unfold ...; intros ...; Intros.` to `pre_process`
  - replaced the stale `intros j ...` tail with the packaging pattern used in `CAV/examples/string_is_empty`
  - compared both model-level and entailment-level heap transport approaches
  - corrected rewrite directions once the target order was re-identified as `i ** (a ** b)`
- Result:
  - `proof_of_string_equal_entail_wit_3_1` is still the first blocker
  - `proof_manual.v` remains uncompilable, so `goal_check.v` still cannot be compiled successfully
  - non-`.v` files under `coq/` were cleaned again after the failed probe

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_003208_string_equal/logs/codex_stderr_20260419_011913.log`
- Detail: `external codex run exceeded remaining timeout budget of 775 seconds`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_003208_string_equal/logs/codex_stderr_20260419_013208.log`
- Detail: `external codex run exceeded remaining timeout budget of 1 seconds`

## Issue 8: the latest blocker had moved from old bridge witnesses to invalid return-witness proof tails

- Phenomenon:
  - the retry-round prose in `issues.md` and `proof_reasoning.md` still described `proof_of_string_equal_entail_wit_3_1` as the active blocker
  - but the current `logs/compile_proof_manual.log` showed a newer first stable error at `proof_of_string_equal_return_wit_1`, line 516:
    - `The relation derivable1 is not a declared symmetric relation.`
- Trigger:
  - several return witnesses started with bare `symmetry.` after `pre_process`
  - at that point the goal was still an entailment (`derivable1`), not a plain equality, so Coq tried to flip the outer entailment relation instead of the inner `string_equal_spec` equation
- Localization:
  - `output/verify_20260419_003208_string_equal/coq/generated/string_equal_proof_manual.v`
  - initially `proof_of_string_equal_return_wit_1`, then the follow-on return witnesses
- Fix:
  - removed the invalid entailment-level `symmetry.` uses from the return witnesses
  - rewrote the return proofs to establish explicit spec facts in their helper-lemma orientation and then rewrite the target equalities
  - restored `CharArray.full_length` bridges where the helper lemmas needed `Zlength la = na` / `Zlength lb = nb`
  - converted the generated `Z.of_nat (length (...)) = ...` facts back to `Zlength` equalities using `Zlength_correct`, `Zlength_app`, `Zlength_cons`, and `Zlength_nil`
  - fixed several local witness-shape mismatches:
    - the preserved prefix hypothesis had to be rewrapped from `0 <= j < n -> ...` to `0 <= j -> j < n -> ...`
    - one `nb = na` rewrite in `return_wit_2` needed the reverse direction
    - `return_wit_5` was closed by contradiction once `Zlength la = na` made `Znth na (la ++ [0]) 0 <> 0` impossible
    - `return_wit_6` needed the symmetric `string_equal_spec_zero_nonzero` proof over `lb` and `la`, followed by `string_equal_spec_sym`
- Result:
  - `proof_manual.v` now compiles successfully
  - the full compile chain now succeeds:
    - `original/string_equal.v`
    - `coq/generated/string_equal_goal.v`
    - `coq/generated/string_equal_proof_auto.v`
    - `coq/generated/string_equal_proof_manual.v`
    - `coq/generated/string_equal_goal_check.v`
  - `proof_manual.v` still contains no `Admitted.` and no added `Axiom`
  - non-`.v` artifacts under `output/verify_20260419_003208_string_equal/coq/` were deleted again after the successful compile

## Final state after successful retry completion

- The active annotated C file remained unchanged in this retry round.
- No new `symexec` run was needed because the annotations and generated goals stayed aligned.
- Verification now succeeds in the existing workspace:
  - `goal.v`: success
  - `proof_auto.v`: success
  - `proof_manual.v`: success
  - `goal_check.v`: success
- `coq/` contains only `.v` files after cleanup.
