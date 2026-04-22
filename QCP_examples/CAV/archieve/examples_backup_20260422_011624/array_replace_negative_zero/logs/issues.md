# Issues

## 2026-04-20T15:36:52+08:00

- Initial symbolic-execution invocation used space-separated long options and failed with `goal file not specified`. Re-ran with `--flag=value` options, including `--goal-check-file`, and symbolic execution completed successfully.
- The input needed a loop invariant relating processed prefix and unprocessed suffix lists. Added a prefix/suffix invariant to the active annotated C file with preservation for negative and nonnegative original values.
- Generated manual proof obligations initially contained `Admitted.` placeholders. Replaced them with a helper list-extensionality lemma and explicit proofs for initialization, negative branch, nonnegative branch, and return.
- Coq proof iteration exposed brittle rewrites around `Zlength_app` after `app_Znth2` simplification. Replaced mandatory rewrites with focused list-length reasoning and explicit implication subproofs.
- Return proof initially referenced the wrong generated hypothesis after `pre_process`; corrected it to use the invariant postcondition hypothesis.

Resolution: all generated Coq files required by the workflow compile, and `array_replace_negative_zero_goal_check.v` compiles successfully.
