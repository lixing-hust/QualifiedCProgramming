# Contract Reasoning: count_digits

## Source Semantics

The raw task defines `count_digits(int n)` for nonnegative integers. The special case is `n == 0`, which returns `1`. For positive `n`, the function repeatedly divides `n` by `10` and counts how many positive quotients are visited before reaching `0`.

The supplied implementation is already verification-friendly: it is a single scalar function, uses only local variables, has no pointer or heap access, and has no I/O or external state.

## Input Domain and Boundaries

- Required input domain: `0 <= n`.
- C integer safety domain: `n <= INT_MAX`.
- `cnt` starts at `0` and is incremented once per decimal digit for positive inputs. Under `n <= INT_MAX`, the result is at most the decimal digit count of `INT_MAX`, so `cnt++` cannot overflow.
- Division uses C integer division on nonnegative values, matching Coq `Z.quot` for the modeled nonnegative path.

## Postcondition Semantics

The postcondition should state exactly the returned decimal digit count of the original input:

- `count_digits_z(0) = 1`
- for positive `n`, `count_digits_z(n)` is the number of repeated divisions by `10` needed to reach `0`

The C contract therefore imports a small topic-specific Coq function `count_digits_z` and ensures `__return == count_digits_z(n@pre)`.

## Coq Dependency Decision

No existing reusable public Coq function for this exact decimal digit-count semantics was found in the local inputs or examples. A small `input/count_digits.v` is therefore necessary. It contains only the topic-specific mathematical definition, with fuel bounded by `Z.to_nat n`, and no verification-stage lemmas or proof scaffolding.

## Memory

The function does not read or write heap memory. Both precondition and postcondition use `emp`.
