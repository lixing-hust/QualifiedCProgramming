# Reasoning: climbStairs

## Problem understanding
- Function `climbStairs(n)` returns the number of distinct ways to reach step `n` when each move is `+1` or `+2`.
- Raw statement fixes boundary behavior:
  - `n = 0` -> `1`
  - `n = 1` -> `1`
- Given implementation is iterative DP with rolling variables and should be preserved.

## Mathematical semantics
- Let `ways(0) = 1`, `ways(1) = 1`.
- For `n >= 2`, `ways(n) = ways(n-1) + ways(n-2)`.
- This is Fibonacci-shifted (`ways(n) = Fib(n+1)` under `Fib(1)=Fib(2)=1`).

## Contract design decisions
- No pointers or heap states are involved, so memory condition is `emp` in pre/post.
- Need integer safety constraints for C `int` arithmetic.
- Largest safe result for 32-bit signed int:
  - `ways(45) = Fib(46) = 1836311903` (safe)
  - `ways(46) = Fib(47) = 2971215073` (overflow)
- Therefore precondition should include `0 <= n <= 45`.
- This also ensures every loop addition `prev1 + prev2` stays within int range.

## Whether `.v` is needed
- In this leetcode workspace, no existing shared Coq symbol for climb-stairs semantics was found.
- Following annotate rules, create a minimal task-specific `input/climb_stairs.v` that defines a Coq function `climb_stairs_z : Z -> Z`.
- C spec can then directly use `__return == climb_stairs_z(n@pre)`.

## Output shape
- `input/climb_stairs.c`: verification-friendly C containing only target function and complete `Require/Ensure`.
- `input/climb_stairs.v`: minimal semantic bridge (no proof obligations, no verify-stage artifacts).
