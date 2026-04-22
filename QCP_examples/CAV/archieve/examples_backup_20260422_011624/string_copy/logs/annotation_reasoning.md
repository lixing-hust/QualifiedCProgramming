# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next character index to inspect and copy, so at the loop head the processed region is the prefix of length `i`.
- Required postcondition: on exit, `dst` must contain exactly `app(l, cons(0, nil))` while `src` stays unchanged.
- Stable facts that should stay in the invariant:
  - bounds `0 <= i <= n`
  - unchanged parameters `src == src@pre`, `dst == dst@pre`, and `n == n@pre`
  - the full source string `CharArray::full(src, n + 1, app(l, cons(0, nil)))`
  - a split description of `dst`: copied prefix from `l`, plus an untouched suffix
- Candidate semantic summary for `dst`:
  - choose a list `l1` for the copied prefix and `d1` for the current suffix
  - keep `Zlength(l1) == i`
  - keep `Zlength(d1) == n + 1 - i`
  - keep `CharArray::full(dst, n + 1, app(l1, d1))`
  - require `(forall (k: Z), (0 <= k && k < i) => l1[k] == l[k])`
- Initialization check: at `i == 0`, choose `l1 = nil` and `d1 = d`; the copied-prefix property is vacuous.
- Preservation expectation: if `src[i] != 0`, then `i < n` because the source list is `l ++ [0]`. Reading `src[i]` and writing it into `dst[i]` should extend the copied prefix from length `i` to length `i + 1`.
- Exit usefulness: when the guard is false, the source value at `i` is `0`. Combined with the invariant, this should let one final store set `dst[i]` to `0`, giving the complete destination string.

## Planned edit

- Add one loop invariant describing the copied prefix of `dst`.
- Add a bridge assertion before the loop body to expose `src[i]` and `dst[i]`.
- Add a bridge assertion after the write so the next loop head regains full-array shape.
- Add one assertion after the loop to fix `i == n` and the final destination shape before writing the terminator.

## Round 2

- The first `symexec` rerun did not reach VC generation because the parser rejected the concrete token `'\0'` in the annotated copy.
- This is not a contract issue. The same control-flow meaning can be preserved by using integer `0` in the active annotated file.
- Fix direction:
  - replace the loop guard `src[i] != '\0'` with `src[i] != 0`
  - replace the final store `dst[i] = '\0'` with `dst[i] = 0`
  - keep the verification annotations unchanged and rerun `symexec`

## Round 3

- After fixing the literal token, the parser still failed at the `while (src[i] != 0)` header before any VC generation.
- Existing repository examples show that this frontend accepts `while (1)` plus inner `if (...) break;` patterns, and it also accepts indexed character reads in `if` statements.
- This suggests the issue is the indexed character expression in the loop header, not the loop body itself.
- Fix direction:
  - rewrite the annotated control flow to `while (1) { if (src[i] == 0) break; ... }`
  - keep the invariant at the loop head and preserve the same copied-prefix meaning
  - if symbolic execution then reaches the VC layer, continue from those witness obligations instead of changing control flow again

## Round 4

- Rewriting the loop header did not move the parser failure; it still stopped at the loop token itself.
- That strongly suggests the issue is in the invariant syntax immediately preceding the loop, not in the C control flow.
- To isolate the frontend limitation, the next step is to temporarily shrink the invariant to a minimal, definitely parseable shape:
  - keep only bounds, unchanged-parameter equalities, and the original full-array predicates
  - remove existentially split destination state and quantified prefix semantics
- If this parses, then the parser limitation is in one of the richer invariant constructs, and I can add them back incrementally. If it still fails, the problem is even more basic and the verify task is blocked at the annotation frontend rather than the proof layer.

## Round 5

- The real parser issue was subtler: the invariant used `n@pre`, but `n` comes from the `With` binder, not from a mutable C variable. In this annotation language, that means `n` should be used directly.
- Once the scratch probe switched from `n@pre` to `n`, the parser advanced into symbolic execution and exposed the expected semantic obligations instead of stopping at the loop token.
- A second probe showed that a copy-array-style whole-list rewrite using `sublist` is not accepted cleanly here for this char-array case, but the existential split form is accepted:
  - `exists l1 d1`
  - copied prefix length `Zlength(l1) == i`
  - remaining suffix length `Zlength(d1) == n + 1 - i`
  - copied-prefix value relation `(forall k < i, l1[k] == l[k])`
  - destination ownership `CharArray::full(dst, n + 1, app(l1, d1))`
- This accepted shape is also strong enough for `symexec` to finish without any extra `which implies` bridge assertions in the loop body.

## Final annotation choice

- Keep the control flow in the annotated copy as:
  - `while (1)`
  - `if (src[i] == 0) break;`
  - `dst[i] = src[i];`
  - `i++;`
- Keep the loop invariant as the existential split over the destination array with plain `n`, not `n@pre`.
- Do not add an extra loop-exit assertion unless later Coq obligations prove it is necessary.

## Round 6

- The later proof failure at `return_wit_1` showed that the previous invariant was still too weak for the postcondition.
- The missing fact is not destination shape; it is source-string progress:
  - at loop exit we know `src[i] == 0`
  - to conclude this `0` is the final terminator position, we also need to know every earlier source character was nonzero
- Under the current invariant, the proof only remembers:
  - copied prefix equality `l1[k] == l[k]` for `k < i`
  - destination split shape
  - bounds `0 <= i <= n`
- That is not enough to derive `i = n`, because the proof has forgotten that the loop would already have stopped at any earlier zero.
- The fix direction is therefore to strengthen the invariant with an explicit nonzero-prefix fact:
  - `(forall (k: Z), (0 <= k && k < i) => l[k] != 0)`
- This preserves the same control-point meaning:
  - initialization is vacuous at `i = 0`
  - preservation is immediate from the branch condition `src[i] != 0` and prefix equality
  - on exit, `l[i] == 0` together with all earlier `l[k] != 0` forces `i = n`
- After adding that fact, rerun `symexec` from a clean generated directory before touching `proof_manual.v` again.

## Round 7

- Contract was then strengthened at the input layer as well:
  - `forall (k: Z), (0 <= k && k < n) => l[k] != 0`
- The active annotated copy must stay aligned with the formal input contract, so the same strengthened precondition was copied into `annotated/verify_20260418_124259_string_copy.c`.
- This does not change the control-flow reasoning, but it removes the earlier mismatch where Verify was trying to prove against a stronger local invariant than the current annotated contract stated.
- After syncing the annotated contract with `input/string_copy.c`, the next step is again:
  - clear generated files
  - rerun `symexec`
  - continue proof on the refreshed VC

## Round 8

- The refreshed VC still did not carry enough information into `return_wit_1`.
- Diagnosis:
  - the strengthened contract states `forall 0 <= k < n, l[k] != 0`
  - but the invariant only preserved the weaker prefix-local fact `forall 0 <= k < i, l[k] != 0`
  - at loop exit this is not enough to refute the case `i < n`, because it says nothing about position `i` itself
- The missing piece is therefore not in the contract anymore, but in the invariant:
  - Verify must also preserve the contract-level pure fact unchanged
- Fix direction:
  - add the full-string nonzero fact directly to the invariant:
    - `forall (k: Z), (0 <= k && k < n) => l[k] != 0`
  - keep the prefix-local fact as well, since it is still the natural loop-progress summary
- This is initialization-safe and preservation-safe because `l` and `n` are logical inputs and never change during the loop.
