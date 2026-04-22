# Verification Issues

## Issue 1: first invariant used unsupported list syntax in the annotation parser

- Phenomenon:
  - the first `symexec` retry failed before VC generation
  - `logs/qcp_run.log` reported `unexpected PT_NATLIT, expecting PT_RPAREN or PT_COMMA`
- Trigger condition:
  - the invariant used `string_contains_char_spec(sublist 0 i l, c) == 0`
- Localization:
  - active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_182117_string_contains_char.c`
- Diagnosis:
  - this front end requires the concrete function-call form `sublist(0, i, l)`
- Fix action:
  - rewrote the attempted prefix expression to the function-call form
- Result:
  - the parser moved past that exact syntax error, but a second front-end issue remained

## Issue 2: `sublist` still failed inside this custom string-spec invariant

- Phenomenon:
  - the next `symexec` retry failed with `Use of undeclared identifier 'sublist'`
- Trigger condition:
  - the invariant still depended on `sublist(0, i, l)` under `string_contains_char_spec`
- Diagnosis:
  - for this task, the safer accepted encoding is the existential prefix/suffix split already used in nearby examples
- Fix action:
  - rewrote the invariant to:
    - `exists l1 l2`
    - `l == app(l1, l2)`
    - `Zlength(l1) == i`
    - `string_contains_char_spec(l1, c) == 0`
- Result:
  - `symexec` succeeded and generated fresh `goal/proof_auto/proof_manual/goal_check`

## Issue 3: manual proof blocked in `proof_of_string_contains_char_entail_wit_2`

- Phenomenon:
  - `proof_manual.v` no longer contains `Admitted.`, but Coq compilation initially still failed
  - first stable compile error:
    - file: `coq/generated/string_contains_char_proof_manual.v`
    - line: around the existential witness branch of `proof_of_string_contains_char_entail_wit_2`
    - message: `Tactic failure: Cannot find witness.`
- Trigger condition:
  - after choosing the next prefix/suffix witness for the continue branch, the post-`entailer!` arithmetic/witness obligations are still not aligned with the current script
- Localization:
  - failing compile log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_182117_string_contains_char/logs/compile_proof_manual.log`
  - reasoning trace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_182117_string_contains_char/logs/proof_reasoning.md`
- Diagnosis:
  - the invariant itself is good enough for symbolic execution
  - the unresolved blocker is a manual-proof witness packaging issue in the continue branch, not a contract or annotation permission gap
- Fix attempts already made:
  - added local helper lemmas for extending a prefix with a nonmatching character and for the hit case
  - recovered `Zlength l = n` via `CharArray.full_length`
  - normalized the boundary `Znth` contradiction when proving `i < n`
  - simplified several stale rewrites and old-Coq syntax incompatibilities in the manual script
- Final fix:
  - inspect `entail_wit_2` in `coqtop` and observe that the continue branch left three pure goals after `entailer!`
  - prove them in the correct order:
    - spec-preservation
    - prefix length
    - prefix/suffix recombination
  - then repair two later stale rewrites in `return_wit_1` and `return_wit_2`
- Current result:
  - `original/<name>.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile successfully

## Issue 4: cleanup status

- Action:
  - removed all non-`.v` files under the current workspace `coq/` tree after the successful final compile
- Result:
  - `find .../coq -type f ! -name '*.v'` is empty
