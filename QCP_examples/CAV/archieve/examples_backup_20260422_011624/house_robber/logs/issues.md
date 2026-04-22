# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes
- Final verification result: `goal_check.v` compiled successfully.

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was freshly initialized with placeholder metadata.
- Localization: `output/verify_20260421_134943_house_robber/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, filled in a semantic description for a dynamic-programming array scan, and used only controlled vocabulary values. After final verification, added `verification_status: goal_check_passed`.
- Result: the fingerprint now has non-empty semantic content and controlled keywords.

## Annotation Layer

- Phenomenon: the active annotated copy had no loop invariant for `for (i = 0; i < n; ++i)`.
- Trigger: the postcondition requires connecting `prev1` to `house_robber_spec(l)` and preserving `IntArray::full(a, n, l)` through the array scan.
- Localization: `annotated/verify_20260421_134943_house_robber.c`, loop before line 37 in the initial annotated copy.
- Fix: appended detailed reasoning to `logs/annotation_reasoning.md` and added an invariant with loop bounds, parameter preservation, `prev1 == house_robber_spec(sublist(0, i, l))`, `prev2 == house_robber_spec(sublist(0, i - 1, l))`, accumulator range bounds, and `IntArray::full(a, n, l)`.
- Result: after two annotation repairs, `symexec` completed successfully and generated fresh Coq files.

## Annotation Parser: Undeclared Coq Function

- Phenomenon: the first `symexec` run failed with `Use of undeclared identifier 'house_robber_acc'`.
- Trigger: the invariant referenced `house_robber_acc`, but the input C only declares `house_robber_spec` as an `Extern Coq` symbol.
- Localization: `annotated/verify_20260421_134943_house_robber.c`, invariant line containing `house_robber_acc`.
- Fix: rewrote the invariant to use `house_robber_spec(sublist(...))`.
- Result: the undeclared identifier error was removed.

## Annotation Parser: Implication Shape

- Phenomenon: the second `symexec` run failed with `Cannot unify types Assertion and Prop`.
- Trigger: the invariant used split implication clauses for `i == 0` and `1 <= i` inside a long assertion conjunction.
- Localization: `annotated/verify_20260421_134943_house_robber.c`, invariant lines for `prev2`.
- Fix: replaced the split implication form with the uniform previous-prefix expression `prev2 == house_robber_spec(sublist(0, i - 1, l))`.
- Result: the next clean `symexec` pass succeeded.

## Symexec Invocation

- Phenomenon: verification needed a clean symbolic execution after each annotation change.
- Trigger: the workflow requires regenerated `goal`, `proof_auto`, `proof_manual`, and `goal_check` files after annotation edits.
- Localization: `logs/qcp_run.log` and `coq/generated/`.
- Fix: removed stale generated files and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--input-file`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_134943_house_robber`, and `--no-exec-info`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## Manual Proof

- Phenomenon: `house_robber_proof_manual.v` contained five `Admitted.` placeholders after successful `symexec`.
- Trigger: the generated VCs required list recurrence facts for `house_robber_spec`, prefix-sum bounds for overflow/range obligations, branch-specific `Z.max` reasoning, and a final `sublist_self` bridge.
- Localization: `coq/generated/house_robber_proof_manual.v`.
- Fix: added local helper lemmas for previous accumulator state, the snoc recurrence, nonnegative prefix sums, prefix-sum monotonicity, and prefix-sum snoc. Replaced all five manual witness placeholders with complete proofs.
- Result: `house_robber_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Proof Iteration Details

- Phenomenon: helper proofs repeatedly failed with `Cannot find witness` around `sublist_cons1` and `sublist_split`.
- Trigger: side conditions needed explicit `Zlength_cons`, `Zlength_nonneg`, or `Zlength_correct` bridges.
- Localization: helper lemmas in `coq/generated/house_robber_proof_manual.v`.
- Fix: made length bridges explicit and split the `i = 0` case for the recurrence because `sublist 0 (i - 1)` has a negative upper bound there.
- Result: all helper lemmas compiled.

- Phenomenon: branch witness proofs initially failed because the bullet order did not match the subgoal order after `entailer!`.
- Trigger: `entailer!` emitted prefix-sum bound goals before recurrence-equality goals.
- Localization: `proof_of_house_robber_entail_wit_2_1` and `proof_of_house_robber_entail_wit_2_2`.
- Fix: inspected the goals in `coqtop`, reordered bullets, solved bounds with `sum_prefix_snoc`, then applied the recurrence helper and `Z.max_l`/`Z.max_r` with `symmetry`.
- Result: both branch preservation witnesses compiled.

- Phenomenon: the return witness failed with a setoid rewrite evar error.
- Trigger: rewriting the length equality inside `house_robber_spec (sublist ...)` asked typeclass machinery for unavailable `Proper` instances.
- Localization: `proof_of_house_robber_return_wit_1`.
- Fix: avoided setoid rewrite, used `rewrite H2; f_equal; apply sublist_self`.
- Result: the return witness compiled.

## Compile Replay

- Phenomenon: final verification required compiling all current generated Coq files, including `goal_check.v`.
- Trigger: verify completion criteria require the full compile template and current generated artifacts.
- Localization: `logs/compile.log`.
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260421_134943_house_robber`.
- Result: `original/house_robber.v`, `house_robber_goal.v`, `house_robber_proof_auto.v`, `house_robber_proof_manual.v`, and `house_robber_goal_check.v` compiled successfully.

## Cleanup

- Phenomenon: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260421_134943_house_robber/coq/generated/`.
- Fix: deleted all non-`.v` files under `coq/`.
- Result: only the generated `.v` files remain under `coq/generated/`.
