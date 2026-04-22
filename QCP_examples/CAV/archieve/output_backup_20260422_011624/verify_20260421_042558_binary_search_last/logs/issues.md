# Issues

## 1. Empty workspace fingerprint placeholders

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` keywords.
- Trigger: early verify workflow setup for `binary_search_last`.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a concrete semantic description and used only controlled vocabulary values for search, while-loop, array/pointer, loop invariant, monotonicity, range-bound, case split, heap reasoning, and edge-case behavior.
- Result: fingerprint is non-empty and now also records final verification status values after successful replay.

## 2. Missing loop invariant and bridge assertions

- Phenomenon: the active annotated C copy initially matched the input C and had no `Inv`/`Assert`, so symbolic execution had no stable summary for the binary-search partition or final last-occurrence proof.
- Trigger: first annotation pass on `annotated/verify_20260421_042558_binary_search_last.c`.
- Location: `annotated/verify_20260421_042558_binary_search_last.c`, around the `while (left < right)` loop and the `mid` read.
- Fix action: added an upper-bound-style loop invariant preserving `0 <= left <= right <= n`, unchanged parameters, sortedness, prefix values `<= target`, suffix values `> target`, the exit point fact, and `IntArray::full(a, n, l)`. Added midpoint and else-branch bridge assertions.
- Result: the loop and branch VCs became expressible using the same proof pattern as `upper_bound`/`binary_search_first`.

## 3. Post-loop assertion blocked local variable cleanup

- Phenomenon: first `symexec` after annotation exited with `Fail to Remove Memory Permission of mid:107` at `annotated/verify_20260421_042558_binary_search_last.c:99:8`.
- Trigger: a post-loop assertion had been inserted between the loop and the final `if`.
- Location: `annotated/verify_20260421_042558_binary_search_last.c`, after the `while` loop.
- Fix action: removed the post-loop assertion and relied on the loop invariant plus the final branch condition instead.
- Result: rerunning `symexec` from `/home/yangfp/QualifiedCProgramming` succeeded and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## 4. Initial `symexec` invocation used the wrong working directory

- Phenomenon: the first manual `symexec` command failed immediately with `folder path QCP_examples/ does not exist`.
- Trigger: running the documented `-slp QCP_examples/ SimpleC.EE` command from the workspace directory rather than the project root.
- Location: command execution context for `symexec`.
- Fix action: reran the same command from `/home/yangfp/QualifiedCProgramming`.
- Result: the logical source path resolved correctly; after removing the post-loop assertion, `symexec` completed successfully.

## 5. Manual proof obligations generated as admitted placeholders

- Phenomenon: `binary_search_last_proof_manual.v` contained seven `Admitted.` placeholders for `safety_wit_2`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, `entail_wit_4_1`, `entail_wit_4_2`, and `return_wit_2`.
- Trigger: successful `symexec` generation leaves non-auto witnesses for manual proof.
- Location: `coq/generated/binary_search_last_proof_manual.v`.
- Fix action: added quotient-by-2 helper lemmas, proved safety and loop-preservation obligations with the established binary-search pattern, and proved the no-match return branch by deriving `left = right`, proving `l[left - 1] < target`, then splitting each candidate index into prefix or suffix cases.
- Result: `proof_manual.v` now compiles and contains no `Admitted.` and no `Axiom`.

## 6. Coq syntax error in one `match goal` branch

- Phenomenon: compiling `binary_search_last_proof_manual.v` failed with `Syntax error: ',' or '|-' expected (in [match_context_rule])` at line 161.
- Trigger: a `match goal` pattern for the upper-suffix hypothesis omitted `|- _`.
- Location: `coq/generated/binary_search_last_proof_manual.v:161`.
- Fix action: changed the branch pattern to include `|- _`.
- Result: `proof_manual.v` compiled, and the full replay of `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` completed successfully.

## 7. Coq intermediate files after compilation

- Phenomenon: successful `coqc` generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Trigger: final full Coq compilation.
- Location: `output/verify_20260421_042558_binary_search_last/coq/generated/`.
- Fix action: deleted all non-`.v` files under `coq/` after successful replay.
- Result: `find coq -type f ! -name '*.v'` returns zero files.
