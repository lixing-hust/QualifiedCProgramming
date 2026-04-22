# Contract reasoning: fibonacci

## Source semantics

- Target function: `fibonacci`
- Input: integer `n`
- Problem domain: `n >= 0`
- Mathematical meaning:
  - `fib(0) = 0`
  - `fib(1) = 1`
  - for `n >= 2`, `fib(n) = fib(n - 1) + fib(n - 2)`
- Implementation shape:
  - return `0` directly for `n == 0`
  - keep two rolling states `a` and `b`
  - for each `i` from `2` through `n`, compute `c = a + b`, then shift `a = b`, `b = c`
  - return `b`

## Interface decision

The original interface is already verification-friendly:

```c
int fibonacci(int n)
```

It is a pure scalar computation with no pointer, array, heap, or global-state dependency. No interface rewrite is needed.

## Boundary and overflow decision

The C implementation uses signed `int` arithmetic. To preserve defined C behavior and keep every intermediate addition in range, the contract restricts:

```c
0 <= n && n <= 46
```

`fib(46) = 1836311903` fits in signed 32-bit `int`, while `fib(47) = 2971215073` exceeds `INT_MAX`. Because the recurrence is nondecreasing on this domain, this final-result bound is sufficient for all rolling additions performed by the loop.

## Memory decision

The function uses only local scalar variables. The contract uses `emp` in both precondition and postcondition.

## Coq dependency decision

No reusable public `fib` or `fibonacci` definition was found in the local CAV inputs. The postcondition needs a mathematical recurrence for Fibonacci values, so a task-specific `input/fibonacci.v` is needed.

The C contract will:

- import `fibonacci`
- expose `fib_z : Z -> Z`
- specify `__return == fib_z(n@pre)`

The `.v` file will contain only the task-specific mathematical definition:

- a structurally recursive `fib_pair` definition over `nat`
- a `fib_nat` projection
- a `Z` wrapper using `Z.to_nat`

No loop invariants, assertions, bridge assertions, or Verify-stage hints are included in the contract output.
