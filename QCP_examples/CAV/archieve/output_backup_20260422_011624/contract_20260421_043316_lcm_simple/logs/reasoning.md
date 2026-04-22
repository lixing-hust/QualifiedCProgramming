# Contract reasoning: lcm_simple

## Source semantics

The raw program takes two positive integers `a` and `b`, initializes `x` to `a`, then repeatedly adds `a` until `x % b == 0`. Every value assigned to `x` is a positive multiple of `a`; the loop exits at the first enumerated multiple of `a` that is also divisible by `b`. For positive inputs, this value is the least common multiple of `a` and `b`.

## Boundary conditions

- Inputs must satisfy `1 <= a` and `1 <= b`; this also makes modulo by `b` safe.
- The implementation uses C `int`, so the final LCM must be representable as an `int`.
- Because `x` increases by `a` through positive multiples and stops at the LCM, all intermediate values are between `a` and the final LCM. Bounding `Z.lcm a b` by `INT_MAX` is therefore the natural overflow precondition.
- No pointer or heap memory is used, so the memory predicate is `emp`.

## Coq dependency decision

The C contract should refer to stable problem-specific names rather than embedding all LCM facts directly in the annotation. Coq provides `Z.lcm` after `Require Import ZArith`, so `input/lcm_simple.v` only needs a minimal bridge:

```coq
Definition lcm_simple_value (a b : Z) : Z :=
  Z.lcm a b.

Definition lcm_simple_spec (a b r : Z) : Prop :=
  r = lcm_simple_value a b.
```

No additional helper definitions are needed.

## Contract shape

The generated C input imports `lcm_simple`, exposes `lcm_simple_value` and `lcm_simple_spec`, requires positive inputs and bounded mathematical LCM, and ensures the return value satisfies the LCM specification over the pre-state inputs.
