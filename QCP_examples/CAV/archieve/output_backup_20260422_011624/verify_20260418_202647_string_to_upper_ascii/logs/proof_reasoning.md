# Proof Reasoning

## Iteration 1: witness shape after successful `symexec`

- Generated manual obligations:
  - `entail_wit_1`
  - `entail_wit_2_1`
  - `entail_wit_2_2`
  - `entail_wit_2_3`
  - `entail_wit_3`
- Diagnosis:
  - these are exactly the logical transitions induced by the chosen invariant
  - no missing ownership shape appears in the witnesses, so this is a proof-layer task rather than a reason to go back and redesign annotations
- Expected proof split:
  - `entail_wit_1`: initialize the invariant with `l1 = nil`, `l2 = l`
  - `entail_wit_2_1`: write-branch step, where the current suffix head is in `97 .. 122`
  - `entail_wit_2_2`: continue branch with current head `< 97`, so the step extends the processed prefix without changing the current character value
  - `entail_wit_2_3`: continue branch with current head `> 122`, same shape as the previous one
  - `entail_wit_3`: exit branch, where the current unread value is `0`, forcing the remaining suffix to be empty
- Planned helper lemmas:
  - `string_to_upper_ascii_spec_length`
  - `string_to_upper_ascii_spec_app`
  - local arithmetic lemmas for `upper_ascii_char`
- Why helper lemmas are preferable here:
  - the main witnesses should only do `Exists`, `destruct` on the remaining suffix, `rewrite`, and `entailer!`
  - the recursive list reasoning is reusable across both continue branches and the write branch

## Iteration 2: first `coqc` replay exposed proof-state details

- First stable compile blocker:
  - the old parser rejected compact proof syntax such as:
    - `Exists a, b`
    - `destruct ... as [...]`
- Fix:
  - normalized the script to one `Exists` per line
  - switched case splits to the older `destruct l2_2.` style
- After that, `coqtop` on `entail_wit_2_1` showed the real nil-branch context:
  - after `destruct l2_2`, the impossible branch still carries
    - `H2 : Znth i (string_to_upper_ascii_spec l1_2 ++ 0 :: nil) 0 <> 0`
    - `H6 : Zlength l1_2 = i`
- Why that matters:
  - this means the nil branch should not be closed by a generic `contradiction`
  - it needs an explicit rewrite showing the current index lands exactly on the trailing sentinel `0`
- Next patch direction:
  - rewrite with `app_Znth2`
  - use `string_to_upper_ascii_spec_length`
  - reduce the shifted index to `0`
  - finish by contradiction

## Iteration 3: successor branches need explicit length recovery

- The next compile failure left `entail_wit_2_1` incomplete after `entailer!`.
- Interpretation:
  - the remaining VC was not about the list rewrite yet
  - it still needed a pure bound such as `i + 1 <= n`, which is not obvious to `entailer!` without first recovering `Zlength l = n`
- Fix direction:
  - use `CharArray.full_length` on the current post-write array state
  - add a local `replace_Znth_length` lemma
  - derive `Zlength l = n`
  - then derive `i < n` from the nonempty remaining suffix shape `l = l1_2 ++ z :: l2_2`
