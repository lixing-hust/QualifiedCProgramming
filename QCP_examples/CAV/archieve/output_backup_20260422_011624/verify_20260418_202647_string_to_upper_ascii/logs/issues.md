# Issues

## Issue 1: the manual proof script had to be downgraded to older Coq syntax

- Phenomenon:
  - the first `coqc` replay stopped on parser errors in `string_to_upper_ascii_proof_manual.v`
  - concrete failures included:
    - `Exists (@nil Z), l.`
    - `destruct l2_2 as [| x l2'].`
- Trigger condition:
  - this environment accepts conservative proof syntax more reliably than compact modern forms
- Diagnosis:
  - the failure was not in the witness logic yet; it was parser compatibility
- Fix:
  - rewrote witness introduction to one `Exists` per line
  - switched case splits to the older `destruct l2_2.` style
- Result:
  - compilation advanced into the real proof obligations

## Issue 2: the impossible empty-suffix branch needed an explicit sentinel contradiction

- Phenomenon:
  - the first proof pass tried to close the `l2_2 = nil` branch with a bare `contradiction`
  - `coqtop` showed the real critical fact was:
    - `Znth i (string_to_upper_ascii_spec l1_2 ++ 0 :: nil) 0 <> 0`
    - together with `Zlength l1_2 = i`
- Trigger condition:
  - the generated witness still carried the current-character nonzero hypothesis at the split point
- Diagnosis:
  - the branch is impossible only after rewriting the current index to the trailing sentinel position
- Fix:
  - rewrote the branch with `app_Znth2`
  - reduced the shifted index to `0`
  - then discharged the contradiction on `Znth 0 (0 :: nil) 0 <> 0`
- Result:
  - the nil branch is now justified by an explicit proof-state argument rather than a guessed contradiction

## Issue 3: the successor branches still need a stable arithmetic bridge from the generated length witness

- Phenomenon:
  - after the parser fixes and nil-branch fix, `coqc` still fails in `proof_of_string_to_upper_ascii_entail_wit_2_1`
  - the current stable compile failure is:
    - `Tactic failure: Cannot find witness.`
- Trigger condition:
  - the proof must recover `Zlength l = n` and then `i + 1 <= n` from:
    - the generated `CharArray.full_length` fact
    - the split equality `l = l1_2 ++ z :: l2_2`
    - the split-length fact `Zlength l1_2 = i`
- Diagnosis:
  - this is a real remaining proof obligation, not a missing load-path or parser issue
  - the current script partially normalizes the generated length hypothesis, but the arithmetic bridge is still incomplete
- Fix attempt chain:
  - added local helper lemmas:
    - `string_to_upper_ascii_spec_length`
    - `string_to_upper_ascii_spec_app`
    - `replace_nth_length`
    - `replace_Znth_length`
    - range lemmas for `upper_ascii_char`
  - used `coqtop` probes to inspect the actual generated context after `pre_process` and `prop_apply CharArray.full_length`
  - rewrote the length normalization to use `Zlength_app`, `Zlength_cons`, and the split equality
- Result:
  - unresolved
  - `symexec` succeeded and the proof script is materially closer, but `string_to_upper_ascii_proof_manual.v` still does not compile
  - because of that, `goal_check.v` also cannot compile

## Final state

- `symexec` succeeded on the current annotated file.
- Fresh generated files exist for:
  - `string_to_upper_ascii_goal.v`
  - `string_to_upper_ascii_proof_auto.v`
  - `string_to_upper_ascii_proof_manual.v`
  - `string_to_upper_ascii_goal_check.v`
- `coq/` non-`.v` intermediates were cleaned.
- Verification is still incomplete because the manual proof remains unresolved.
