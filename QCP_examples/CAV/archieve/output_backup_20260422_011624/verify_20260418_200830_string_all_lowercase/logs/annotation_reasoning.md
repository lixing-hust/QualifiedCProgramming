# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next character index to inspect, so the processed region at the loop head is exactly `sublist(0, i, l)`.
- Required postcondition: return `1` exactly when every character in `l` lies in the lowercase ASCII range `[97, 122]`, while preserving the original `CharArray::full`.
- Stable facts worth preserving at the loop head:
  - `0 <= i <= n`
  - `s == s@pre`
  - the contract fact that all `l[k]` for `0 <= k < n` are nonzero
  - unchanged full ownership of `s`
  - the semantic summary `string_all_lowercase_spec(sublist(0, i, l)) == 1`
- Why this summary is useful:
  - initialization is immediate because `sublist(0, 0, l) = nil` and the spec on `nil` is `1`
  - on the continue branch, the branch conditions show the current element is lowercase, so the processed-prefix spec should stay `1` after extending the prefix by one element
  - on the early-return branch, the branch conditions directly witness a non-lowercase character, so the function should be able to return `0`
  - on the break branch, `s[i] == 0` together with the nonzero-prefix contract should force `i = n`; then the processed-prefix summary becomes the full-list summary needed for return `1`

## Planned edit

- Add only the loop invariant above.
- Do not add extra `Assert` or `which implies` until `symexec` shows they are necessary.

## Round 2

- First `symexec` result:
  - `fatal error: Use of undeclared identifier 'sublist'`
- Diagnosis:
  - the nested term `string_all_lowercase_spec(sublist(0, i, l))` was accepted syntactically in other integer-array examples, but this frontend rejected it in the current string-scanning VC.
  - this is a parser/frontend limitation, not a semantic reason to keep the same shape.
- Revised invariant direction:
  - replace the recursive-prefix summary with the directly needed pure fact
    - `forall k < i, 97 <= l[k] <= 122`
  - keep the original nonzero-string contract fact and full ownership unchanged
  - add a loop-exit assertion fixing `i == n`, so the processed-prefix fact becomes the full-string fact required for the final proof
- Why this still supports the proof:
  - initialization is immediate because the quantified prefix is empty at `i == 0`
  - preservation follows by extending the processed prefix with the current branch fact `97 <= s[i] <= 122`
  - on break, `s[i] == 0` plus the contract fact that every `l[k]` for `k < n` is nonzero rules out `i < n`, so with `i <= n` we get `i == n`
