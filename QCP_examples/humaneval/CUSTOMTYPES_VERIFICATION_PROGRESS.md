# CustomTypes Verification Progress

| Case | Status | Original spec bridge | Notes |
| --- | --- | --- | --- |
| C_111 | full-chain passed | Directly bridges `spec/111.v` `problem_111_pre` / `problem_111_spec` | Input remains `const char *test`; only QCP-facing count initialization and pointer-return adaptations were made. The counting, maximum-frequency selection, and output construction logic are unchanged. All 13 manual witnesses are `Qed`, and a `/tmp` freshness symexec matched the generated goal, auto proof, and goal-check files byte-for-byte. |
| C_22 | full-chain passed | Directly bridges `spec/22.v` `problem_22_pre` / `problem_22_spec` | QCP interface represents each `PyValue` by parallel tag and integer-payload arrays and returns `IntArray *`; the filtering loop, order, duplicates, and output length semantics are unchanged. `/tmp` freshness symexec matched the generated goal, auto proof, and goal-check files byte-for-byte. All four manual witnesses are `Qed`. |

## C_111 verification notes

- The verified function keeps the original `const char *test` input. The unsupported aggregate initializer `int count[256] = {0}` is represented by an explicit 256-element zeroing loop, and the by-value `CharIntMap` result is adapted to an allocated `CharIntMap *` result.
- The original scan, exact character counts, maximum-frequency computation, and output traversal/order are retained. Verification-only annotations strengthen integer bounds, array contents, and loop-state facts without changing runtime behavior.
- `problem_111_pre_z` and `problem_111_spec_z` directly call the numbered `spec/111.v` pre/spec; `histogram_spec_bridge_111` connects the operational count/max/output state to that original specification.
- All 13 manual witnesses are `Qed`. The formal chain `coins_111.v -> C_111_goal.v -> C_111_proof_auto.v -> C_111_proof_manual.v -> C_111_goal_check.v` passes under Coq 8.20.1.
- A non-mutating `/tmp` symbolic-execution rerun reached EOF and produced byte-identical goal, auto-proof, and goal-check files. Exact scans found no `Admitted.`, `Abort.`, `Show.`, case-local `Axiom`, `Parameter`, or diagnostic split goal in the handwritten proof path.

## C_22 verification notes

- The original C `PyValue` array contains fields that the function never reads. The verified QCP interface exposes only the tag array and integer-payload array while retaining a ghost `list py_value` through `py_value_tags` and `py_value_payloads`.
- `problem_22_pre_z` directly calls `problem_22_pre`; `problem_22_spec_z` directly calls `problem_22_spec` with `map PyInt output`.
- `filter_tagged_encoded` and `problem_22_spec_filter_integer_values` prove that the operational loop result satisfies the original numbered specification.
- Generic allocation wrappers replace raw `malloc`; the original filter condition, stable order, duplicate preservation, and one-pass loop remain unchanged.
- The formal chain is `coins_22.v -> C_22_goal.v -> C_22_proof_auto.v -> C_22_proof_manual.v -> C_22_goal_check.v` under Coq 8.20.1.
- Exact scans found no `Admitted.`, `Proof. Abort.`, `Show.`, case-local `Axiom`, or `Parameter` in `coins_22.v`, `C_22_proof_manual.v`, `C_22_goal_check.v`, or `C_22.c`.
- `Print Assumptions` reports both specification bridge lemmas closed under the global context. The representative return witness uses only imported QCP address/size and functional-extensionality assumptions.
