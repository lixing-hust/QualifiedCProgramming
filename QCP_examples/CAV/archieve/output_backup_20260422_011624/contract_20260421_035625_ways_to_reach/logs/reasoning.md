## Contract reasoning

Target: `ways_to_reach`

Raw source: `raw/ways_to_reach.md`

### Semantics

The function computes the number of ways to reach stair `n` when each move advances by either 1 or 2 steps.

The mathematical recurrence is:

- `ways(0) = 1`
- `ways(1) = 1`
- for `n >= 2`, `ways(n) = ways(n - 1) + ways(n - 2)`

The C implementation keeps two adjacent recurrence values:

- `a` starts as `ways(0)`
- `b` starts as `ways(1)`
- each loop iteration computes `c = a + b`, then shifts `a = b`, `b = c`

For `n == 0`, the function returns `1` before the loop. For `n == 1`, the loop is skipped and the function returns the initial `b = 1`. For `n >= 2`, after the loop reaches `i == n`, `b` is `ways(n)`.

### Input domain and overflow

The natural problem domain is `n >= 0`. Since the C return type and all accumulators are `int`, the contract must also ensure every computed value stays within signed 32-bit range.

This recurrence is Fibonacci-shifted: `ways(n) = fib(n + 1)` with `fib(0) = 0`, `fib(1) = 1`. The largest `n` whose result fits in signed 32-bit `int` is `45`:

- `ways(45) = 1836311903`
- `ways(46) = 2971215073`, which exceeds `2147483647`

The loop addition `a + b` computes the next final value for the current index, so bounding `n <= 45` is sufficient for the additions performed by this implementation.

### Memory

The function is pure scalar computation. It does not read or write caller-owned memory, allocate memory, or use global state. The separation-logic heap condition is therefore `emp` in both `Require` and `Ensure`.

### Coq dependency

No existing public Coq function named for this target is available. Although `climb_stairs_z` expresses the same recurrence, depending on another problem's input file would make this target less self-contained. A small target-specific `input/ways_to_reach.v` is justified.

The C contract imports `ways_to_reach` and exposes:

- `ways_to_reach_z : Z -> Z`

The postcondition uses the abstract recurrence value directly:

- `__return == ways_to_reach_z(n@pre)`

No loop invariant, assertion, bridge assertion, or loop-exit assertion belongs in the contract output.
