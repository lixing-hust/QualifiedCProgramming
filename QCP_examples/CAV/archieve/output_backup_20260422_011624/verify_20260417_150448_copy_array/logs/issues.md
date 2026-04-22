# Verify Issues

## Resolved During Verification

- `copy_array_proof_manual.v` initially contained four admitted witness lemmas from `symexec`.
- The nontrivial proof work was confined to list-shape rewrites for the copied prefix:
  - loop-entry entailment reduced `sublist 0 n ld` to `ld`
  - loop-exit reduced `app(sublist(0,n,ls), sublist(n,n,ld))` to `ls`
  - the first bridge lemma required proving that index `i` of `app(sublist(0,i,ls), sublist(i,n,ld))` is `ld[i]`
  - the second bridge lemma required rewriting `replace_Znth` on the destination list and normalizing the source list with `replace_Znth_Znth`
- After these manual proofs, `goal_check.v` compiled successfully.

## Remaining Issues

- None.
