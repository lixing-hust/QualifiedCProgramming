# Verify Issues

## Annotation And Symexec

- Phenomenon: the initial annotated working copy had no loop invariant, so the string-scan loop still needed verify-specific state to connect the scanned prefix with the Coq spec.
- Trigger: `string_all_lowercase` returns early on the first non-lowercase character and otherwise stops on the terminator, so the loop head must preserve both the processed-prefix summary and the untouched full-string ownership.
- Localization:
  - active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260419_001037_string_all_lowercase.c`
  - reasoning log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_001037_string_all_lowercase/logs/annotation_reasoning.md`
- Fix:
  - added one loop invariant with a prefix/suffix split `l == app(l1, l2)`
  - tracked `Zlength(l1) == i`
  - tracked `string_all_lowercase_spec(l1) == 1`
  - preserved the original nonzero-prefix fact and `CharArray::full`
- Result:
  - the next clean `symexec` pass succeeded immediately
  - fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files were generated

## Proof Parser Compatibility

- Phenomenon: the first `coqc` run on `proof_manual.v` failed before checking the actual proof logic.
- Trigger: helper lemmas used compact Ltac branch syntax of the form `destruct ...; [lia |].`
- Localization:
  - file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_001037_string_all_lowercase/coq/generated/string_all_lowercase_proof_manual.v`
  - failing log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_001037_string_all_lowercase/logs/compile_proof_manual.log`
- Fix:
  - rewrote those `destruct` steps into explicit named branches
- Result:
  - the file parsed successfully and the proof failures moved to real witness obligations

## Generated-Hypothesis Alignment

- Phenomenon: several proof attempts failed because the generated witness contexts did not keep the same hypothesis numbering or shapes across different obligations.
- Trigger conditions:
  - `entail_wit_2` did not accept `subst l`; the usable fact was a pure equality that needed `rewrite`
  - `return_wit_1` and `return_wit_2` used different hypothesis numbers after `pre_process` and `entailer!`
  - some `Znth 0 ...` facts needed explicit normalization to the concrete head element before they could be used as arithmetic bounds
- Localization:
  - proof reasoning trace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_001037_string_all_lowercase/logs/proof_reasoning.md`
  - manual proof file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_001037_string_all_lowercase/coq/generated/string_all_lowercase_proof_manual.v`
- Fix actions:
  - switched the preservation proof to `pre_process`
  - derived `Zlength l = n` from `CharArray.full_length`
  - proved `i < n` before the continue-step witness to discharge `i + 1 <= n`
  - used direct helper lemmas for:
    - adding one lowercase character to a verified prefix
    - appending a character below `97`
    - appending a character above `122`
  - normalized current-character hypotheses with explicit `change (Znth 0 ...) with x`
  - adjusted witness proofs to the actual generated hypothesis names in each obligation
- Result:
  - `string_all_lowercase_proof_manual.v` compiled successfully
  - `goal_check.v` then compiled successfully end to end

## Final Outcome

- `symexec` succeeded on the current annotated file.
- `original/string_all_lowercase.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully.
- `proof_manual.v` contains no `Admitted.` and no added `Axiom`.
- Non-`.v` artifacts under `coq/` were deleted after the successful compile pass.
