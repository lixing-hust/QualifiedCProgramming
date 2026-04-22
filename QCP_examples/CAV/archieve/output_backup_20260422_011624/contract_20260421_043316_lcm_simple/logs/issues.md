# Contract issues: lcm_simple

## Resolved

- The raw problem does not state an explicit overflow bound. Added `lcm_simple_value(a, b) <= INT_MAX` as the verification-friendly precondition because all loop values are positive multiples of `a` up to the final LCM.
- The mathematical LCM meaning needs a Coq name usable from the C annotation. Added a minimal `input/lcm_simple.v` bridge using Coq's `Z.lcm`.

## Open

- None for the contract stage.

## Validation

- Checked that `input/lcm_simple.c` contains no `Inv`, `Assert`, `which implies`, bridge assert, or loop-exit assertion.
- Checked the Coq bridge definitions in `coqtop`.
- Ran `gcc -fsyntax-only input/lcm_simple.c`.
