## Iteration 1: recurrence-pair loop invariant

Timestamp: 2026-04-21 03:59:43 +0800

The active annotated file initially has no invariant for the only loop:
`for (i = 2; i <= n; ++i)`. Without an invariant, symbolic execution cannot
summarize the recurrence state carried by `a` and `b` across loop iterations.

Program point:

- active annotated file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_035821_ways_to_reach.c`
- target loop: the `for` loop after the `if (n == 0) return 1;` branch
- first loop guard state: `i == 2`, `a == 1`, `b == 1`

The postcondition requires `__return == ways_to_reach_z(n@pre)`. In the
non-early-return path, the contract gives `0 <= n` and the branch condition gives
`n != 0`, so the loop path has `1 <= n`.

Invariant design:

- preserve the parameter relation `n == n@pre`
- bound the guard-point loop index with `2 <= i && i <= n + 1`
- express the two scalar accumulators as consecutive recurrence values:
  `a == ways_to_reach_z(i - 2)` and `b == ways_to_reach_z(i - 1)`
- preserve only `emp`, because the function uses no heap memory

Initialization:

- before the first guard check, `i == 2`, `a == 1`, and `b == 1`
- `ways_to_reach_z(0) == 1` and `ways_to_reach_z(1) == 1`, matching `a` and `b`
- `1 <= n` gives `2 <= n + 1`

Preservation:

- a loop-body entry also has `i <= n`
- the assignment `c = a + b` computes the next recurrence value
- after `a = b`, `b = c`, and the `++i` update, the next guard state should
  again satisfy the invariant at index `i + 1`

Exit:

- negating `i <= n` while preserving `i <= n + 1` yields `i == n + 1`
- then `b == ways_to_reach_z(i - 1)` becomes
  `b == ways_to_reach_z(n)`, and `n == n@pre` gives the return postcondition

I will first add only this invariant. If the generated return witness cannot
derive the exit equality, the next annotation step should add a minimal
loop-exit assertion immediately after the loop.
