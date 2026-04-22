# Verification Issues

## Summary

- `symexec` succeeded after adding the prefix-count invariant and loop-exit assertion to the annotated C file.
- `count_positive_proof_manual.v` needed five manual witness proofs, all in the expected list/arithmetic layer.
- The final compile chain passed:
  - `count_positive_goal.v`
  - `count_positive_proof_auto.v`
  - `count_positive_proof_manual.v`
  - `count_positive_goal_check.v`
- `count_positive_proof_manual.v` contains no `Admitted.` and no added `Axiom`.
- Non-`.v` files under `coq/` were removed after the successful compile replay.

## Issue 1: `symexec` launch failed at the shell layer first

- Symptom:
  - the first manual rerun exited immediately without producing usable status output
- Trigger condition:
  - the shell command was overescaped while being routed through the terminal tool
- Diagnosis:
  - the verifier itself had not run yet; this was a quoting problem in the wrapper command
- Fix:
  - rerun `symexec` with a plain bash-array argument list instead of an overquoted multiline string
- Result:
  - the next failure reflected the actual workspace state instead of shell noise

## Issue 2: workspace was missing `coq/generated/`

- Symptom:
  - `qcp_run.log` reported:
    - `fatal error: cannot open file .../coq/generated/count_positive_goal.v`
- Trigger condition:
  - this workspace had been created without the `coq/generated/` directory
- Diagnosis:
  - `symexec` had the correct annotated input path, but no destination directory for generated Coq files
- Fix:
  - create `output/verify_20260418_171328_count_positive/coq/generated/`
  - clear any stale generated filenames
  - rerun `symexec` with the canonical repository flags
- Result:
  - fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` were generated

## Issue 3: safety witness needed explicit integer-range bridging

- Symptom:
  - `proof_of_count_positive_safety_wit_4` stayed incomplete after an initial `entailer!`
- Trigger condition:
  - the proof needed to show `cnt + 1 <= INT_MAX`
- Diagnosis:
  - the prefix summary gave `0 <= cnt <= i`, but the proof still needed the stored integer bound on `n_pre`
  - early proof attempts also hardcoded transient hypothesis names and failed for proof-state-shape reasons
- Fix:
  - use `pre_process`
  - recover the `n_pre` range via `store_int_range (&("n")) n_pre`
  - derive the upper and lower bounds for `cnt + 1` explicitly before the final `entailer!`
- Result:
  - the safety witness compiled cleanly and stopped depending on brittle hypothesis numbering

## Issue 4: two witness scripts initially assumed the wrong proof-state shape

- Symptom:
  - compile-driven iterations failed with:
    - `Found no subterm matching ...`
    - `No matching clauses for match`
    - unification on `count_positive_spec (sublist ...)` versus `count_positive_spec l`
- Trigger condition:
  - the first scripts guessed the post-`entailer!` hypotheses for the positive branch and loop-exit witness instead of reading the actual proof state
- Diagnosis:
  - `entail_wit_2_1` already had the branch fact as a pure inequality, so `rewrite H` was the wrong move
  - `entail_wit_3` had already simplified to the pure goal `cnt = count_positive_spec l`, so the right bridge was:
    - `H2 : cnt = count_positive_spec (sublist 0 n_pre l)`
    - `H4 : Zlength l = n_pre`
- Fix:
  - trim `entail_wit_2_1` to destruct `Z_gt_dec (Znth i l 0) 0` directly
  - inspect `entail_wit_3` in `coqtop`
  - rewrite with the generated equalities and then use `sublist_self`
- Result:
  - both witness proofs became short and stable
  - the full compile chain reached `goal_check.v`

## Trace Files

- Symexec log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/qcp_run.log`
- Compile logs:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/compile_original.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/compile_goal.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/compile_proof_auto.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/compile_proof_manual.log`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_171328_count_positive/logs/compile_goal_check.log`
