# Contract reasoning: count_divisors

## Source semantics

The raw task defines `count_divisors(n)` for a positive integer `n`. A positive divisor is any `d` such that `1 <= d <= n` and `n % d == 0`.

The implementation initializes `cnt` to `0`, scans `d` from `1` through `n`, increments `cnt` exactly when `d` divides `n`, and returns `cnt`.

## Interface decision

The original interface is verification friendly:

```c
int count_divisors(int n)
```

It has no pointer arguments, no heap state, no I/O, and no hidden side effects. The target C input should therefore keep the same interface and implementation shape.

## Preconditions

The problem requires `n >= 1`.

The loop condition and update are:

```c
for (d = 1; d <= n; ++d)
```

At the last iteration, `d == n`, and the loop update computes `d + 1`. To avoid signed integer overflow in C, the contract should require `n < INT_MAX`. The counter satisfies `0 <= cnt <= n`, so `cnt++` is also safe under the same bound.

Therefore the function precondition is:

```c
1 <= n && n < INT_MAX && emp
```

## Postcondition

The postcondition should state the exact mathematical result: the return value is the number of integers `d` in `[1, n@pre]` with `n@pre % d == 0`.

There is no existing public Coq function in this workspace for divisor counting, so this task needs a small task-specific Coq definition:

```coq
count_divisors_spec : Z -> Z
```

The C postcondition can then remain compact:

```c
__return == count_divisors_spec(n@pre) && emp
```

## Memory and side effects

The function uses only local integer variables and does not read or write memory through pointers. The heap assertion is `emp` in both precondition and postcondition.

## Coq dependency decision

An `input/count_divisors.v` file is needed because exact divisor-count semantics require a task-specific finite count. The file should only define the mathematical helper and should not contain verification-stage assertions, invariants, or proof scripts.
