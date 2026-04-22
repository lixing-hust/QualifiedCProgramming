# Contract reasoning for `tribonacci`

## Source semantics

The raw task defines the Tribonacci sequence over nonnegative indices:

- `tri(0) = 0`
- `tri(1) = 1`
- `tri(2) = 1`
- for `n >= 3`, `tri(n) = tri(n - 1) + tri(n - 2) + tri(n - 3)`

The provided C implementation keeps a rolling triple `(a, b, c)` initialized to `(tri(0), tri(1), tri(2))`. For every loop index `i` from `3` through `n`, it computes `d = a + b + c` and shifts the triple forward, so after processing `i`, `c` stores `tri(i)`. The early returns cover `n == 0` and `n == 1`; when `n == 2`, the loop is skipped and the function returns the initialized `c == 1`.

## Interface and memory

The original interface `int tribonacci(int n)` is already verification-friendly:

- one scalar input
- one scalar return value
- no pointers or heap memory
- no global state or I/O

The contract therefore only needs `emp` in both precondition and postcondition.

## Input domain and overflow

The raw task states `n >= 0`. The C implementation uses signed `int`, so the contract also needs an upper bound ensuring each computed Tribonacci value remains inside the 32-bit signed `int` range during execution.

The largest safe result for this implementation is `tri(37) = 2082876103`, while `tri(38) = 3831006429` exceeds `INT_MAX`. Because the sequence is nonnegative and increasing after the base cases, requiring `0 <= n <= 37` is the intended overflow boundary for this contract.

## Coq dependency decision

There is no existing public `tribonacci` Coq function in the current inputs. A problem-specific `input/tribonacci.v` is needed to define the mathematical sequence used by the postcondition. The C contract imports this file and states that the return value equals `tribonacci_z(n@pre)`.

The `.v` file contains only the task-specific mathematical definition, written as a structurally recursive rolling triple:

- `tribonacci_triple : nat -> Z * Z * Z`
- `tribonacci_nat : nat -> Z`, selecting the first component
- `tribonacci_z : Z -> Z`, using `Z.to_nat`

No Verify-stage proof hints are included in the contract output.
