## 2026-04-21 invariant addition

Program point: the `while (b != 0)` loop in `annotated/verify_20260421_015041_gcd_iterative.c`.

Current state: the active annotated C file is identical to `input/gcd_iterative.c` and has no loop invariant. A while loop without an `Inv` cannot preserve the semantic relation needed by the postcondition `gcd_iterative_spec(a@pre, b@pre, __return)`. The loop mutates both `a` and `b`, so after the loop the postcondition cannot be recovered from unchanged-parameter facts.

Planned annotation: add an invariant immediately before the loop with an existential `g`, preserving:

- `0 <= a` and `0 <= b`, needed for the `%` step and for the loop state.
- `0 < a@pre + b@pre`, inherited from the precondition so the original problem remains nontrivial.
- `gcd_iterative_spec(a@pre, b@pre, g)`, binding `g` to the original inputs' gcd.
- `gcd_iterative_spec(a, b, g)`, stating that the current Euclidean state has the same gcd.
- `emp`, because the function has no heap ownership.

Why this should fix the current verification point: the invariant holds initially by taking `g = Z.gcd a@pre b@pre`. In a loop body where `b != 0`, the update `(a,b) := (b, a % b)` preserves the gcd by the Euclidean identity. On exit `b == 0`, the invariant gives `gcd_iterative_spec(a, 0, g)` and the return value is `a`, leaving a pure Coq proof obligation that `a = g` and therefore satisfies the original postcondition.
