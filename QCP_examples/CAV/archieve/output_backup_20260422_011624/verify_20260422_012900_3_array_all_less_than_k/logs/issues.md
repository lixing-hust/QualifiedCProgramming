# Issues

## Summary

- Status: completed
- Blocking issues: none remaining
- Annotation changes required: yes
- Manual proof required: no

## Issue 1: workspace fingerprint was initialized with empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and empty `keywords`.
- Trigger condition: the workspace was pre-created before the verify pass and still contained initialization placeholders.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_171937_array_all_less_than_k/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled `semantic_description` and used only controlled-vocabulary keywords for `search`, `for_loop`, `if`, `array`, `pointer`, `preserve_input`, `loop_invariant`, `case_split`, `termination_by_bound`, `heap_reasoning`, and `empty_loop_possible`. After final compilation, added controlled `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint is no longer an empty placeholder and uses only controlled keys and values from the retrieval index.

## Issue 2: loop needed a prefix invariant and loop-exit assertion

- Phenomenon: the active annotated C initially matched the input C exactly and had no invariant for the `for (i = 0; i < n; ++i)` scan.
- Trigger condition: the postcondition for return value 1 requires a universal property over the whole array, while the loop only establishes that fact incrementally over the scanned prefix.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_171937_array_all_less_than_k.c`, immediately before and after the loop.
- Fix: added an invariant recording `0 <= i && i <= n`, unchanged `a`, `n`, and `k`, unchanged `IntArray::full(a, n, l)`, and the checked-prefix fact `(forall j, 0 <= j && j < i => l[j] < k)`. Added a loop-exit assertion fixing `i == n` and rewriting the prefix property to the full range.
- Result: the latest symexec pass completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 3: similar-example lookup initially used the wrong annotated path shape

- Phenomenon: first attempts to read nearby example annotations as `examples/<name>/annotated.c` failed with `No such file or directory`.
- Trigger condition: CAV examples store annotated files under `examples/<name>/annotated/<name>.c`.
- Localization: read-only example lookup for `array_all_zero`, `array_contains`, and `array_any_negative`.
- Fix: reopened the correct paths and used those examples only to confirm the local syntax for prefix invariants and exit assertions.
- Result: no workspace files were affected by the failed read attempts, and the active annotation followed the repository's accepted style.

## Issue 4: generated Coq compilation artifacts required cleanup

- Phenomenon: compiling the generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger condition: standard `coqc` compilation writes binary and auxiliary artifacts next to the generated `.v` files.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_171937_array_all_less_than_k/coq/generated/`.
- Fix: after `goal_check.v` compiled successfully, deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `find output/verify_20260420_171937_array_all_less_than_k/coq -type f ! -name '*.v'` returns no files.
