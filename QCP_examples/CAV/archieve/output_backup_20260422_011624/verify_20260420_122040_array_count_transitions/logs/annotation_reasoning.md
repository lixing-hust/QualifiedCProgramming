## Annotation iteration 1

- Program point: the `for (i = 1; i < n; ++i)` loop in `array_count_transitions`.
- Current issue: the unannotated loop does not preserve the semantic relationship between scalar `cnt` and the Coq list specification required by the postcondition. The verifier also needs the unchanged array resource across all iterations.
- Planned invariant: at the loop condition, `i` is the next adjacent-pair index to inspect, so pairs with indices `1 <= j < i` have already been processed. Therefore `cnt` should equal `array_count_transitions_spec(sublist(0, i, l))`.
- Boundary reasoning: initialization has `i == 1` and `cnt == 0`; for `n = 0`, `sublist(0, 1, l)` is empty because `Zlength(l) == 0`, and for `n >= 1`, a one-element prefix has zero transitions. The invariant uses `1 <= i && i <= n + 1` so the skipped-loop case `n = 0` remains representable.
- Preservation reasoning: when `i < n`, reading `a[i]` and `a[i - 1]` is within bounds. The two branches update `cnt` exactly according to whether the newly appended element differs from the previous last prefix element.
- Exit bridge: after the loop, add a minimal assertion fixing `cnt == array_count_transitions_spec(l)` plus preserved `a`, `n`, and `IntArray::full(a, n, l)`. This covers both normal exit `i == n` for `n > 0` and skipped-loop exit for `n <= 1`.

## Annotation iteration 2

- Symexec feedback: `logs/qcp_run.log` failed at `annotated/verify_20260420_122040_array_count_transitions.c:41:4` with `Fail to Remove Memory Permission of i` after the loop-exit assertion.
- Diagnosis: this matches the documented assertion-placement failure where an assertion after the loop can interfere with local variable permission cleanup. The assertion was intended only to bridge the pure equality `cnt == array_count_transitions_spec(l)`, not to provide new memory shape information.
- Fix: remove the post-loop `Assert` and keep the loop invariant as the only annotation. Any final conversion from `sublist(0, i, l)` to `l` should become a pure Coq witness after successful `symexec` instead of being forced at the C annotation layer.

