## 2026-04-21 annotation pass 1

The unannotated loop is the first verification blocker. The loop control point is immediately before evaluating `x % b != 0`, with `x` representing the current positive multiple of the original `a`. The postcondition is `lcm_simple_spec(a@pre, b@pre, __return)`, which unfolds to equality with `Z.lcm a@pre b@pre` through the supplied Coq input. Therefore the invariant must preserve enough pure arithmetic information to prove that the loop stops exactly at the least positive common multiple, not just at some common multiple.

Planned invariant at the loop head:
- preserve the positive inputs and parameter identity: `1 <= a`, `1 <= b`, `a == a@pre`, `b == b@pre`;
- preserve accumulator shape and range: `1 <= x`, `x <= lcm_simple_value(a,b)`, and `x % a == 0`;
- preserve the body safety bridge: if the loop condition is true, `x + a <= lcm_simple_value(a,b)`, which together with the precondition's `lcm_simple_value(a,b) <= INT_MAX` should justify `x = x + a`;
- preserve minimality of the current search frontier: every positive multiple of `a` smaller than `x` is not divisible by `b`.

Initialization should hold because `x` is initialized to `a`, `a` and `b` are positive, `a` is a positive multiple of itself, and there is no positive multiple of `a` below `a`. Preservation should hold because the body only advances `x` to the next multiple of `a`; the old loop condition records that the old `x` is not divisible by `b`, while the quantified minimality covers all smaller multiples. At loop exit, the invariant plus `x % b == 0` should show `x` is the least positive common multiple and hence equals `lcm_simple_value(a@pre,b@pre)`. I will add this invariant before the `while` and a loop-exit `Assert` directly after the loop to bridge the final return witness.

## 2026-04-21 annotation pass 2

The first generated proof showed that the post-loop `Assert x == lcm_simple_value(a@pre,b@pre) && emp` is at the wrong control point. `lcm_simple_entail_wit_3` had live stack permissions for `a` and `b` on the left but `emp` on the right, leaving the unprovable heap obligation `&( "b") # Int |->_ ** &( "a") # Int |->_ |-- emp` after converting both locations to undef. This matches the assertion guidance warning that loop-exit assertions placed after the loop can interfere with local permission cleanup.

The invariant already contains enough pure arithmetic state for the return witness: `x` is a positive multiple of `a`, no smaller positive multiple of `a` is divisible by `b`, and loop exit gives `x % b == 0`. I will remove the explicit post-loop `Assert` and rerun `symexec` so the final return witness combines the loop-exit facts with the ordinary return/local-cleanup path instead of forcing an impossible standalone assertion entailment.
