# Contract reasoning: power_nonnegative

## Source semantics

- Target function: `power_nonnegative`
- Inputs: integer `base`, integer `exp`
- Problem domain: `exp >= 0`
- Mathematical meaning:
  - `base^0 = 1`
  - for positive `exp`, multiply by `base` exactly `exp` times
- Implementation shape:
  - initialize `ans = 1`
  - loop with `i` from `0` while `i < exp`
  - update `ans = ans * base` on each iteration
  - return `ans`

## Interface decision

The original interface is already verification-friendly:

```c
int power_nonnegative(int base, int exp)
```

The function is a pure scalar computation. It has no heap memory, pointer arguments, aliasing, I/O, global state, or allocation. No interface rewrite is needed.

## Boundary and overflow decision

The raw statement requires only `exp >= 0`, but the C implementation performs signed `int` multiplication at every iteration. The contract therefore adds an integer-safety condition for every prefix power:

```c
forall k, 0 <= k <= exp ->
  INT_MIN <= power_nonnegative_z(base, k) <= INT_MAX
```

This condition covers the initial value `1`, every intermediate value stored in `ans`, and the final return value. It is more precise than imposing an arbitrary small exponent bound, and it supports negative bases as long as each prefix result remains representable as a signed `int`.

The loop update `++i` is safe for all nonnegative `int` values of `exp`: the last executed update is from `exp - 1` to `exp`, so it does not require `exp < INT_MAX`.

## Memory decision

The function uses only local scalar variables. The contract uses `emp` in both precondition and postcondition.

## Coq dependency decision

No reusable power definition was found in the local CAV inputs or examples. The C annotation layer is also clearer with a simple unqualified imported name than with a module-qualified Coq name such as `Z.pow`. A task-specific `input/power_nonnegative.v` is therefore needed.

The C contract will:

- import `power_nonnegative`
- expose `power_nonnegative_z : Z -> Z -> Z`
- require the prefix powers to fit in signed `int`
- specify `__return == power_nonnegative_z(base@pre, exp@pre)`

The `.v` file will contain only the task-specific mathematical definition:

- a structurally recursive `power_nonnegative_nat` over `nat`
- a `Z` wrapper using `Z.to_nat`

No loop invariants, assertions, bridge assertions, `which implies`, or loop-exit assertions are included in the contract output.
