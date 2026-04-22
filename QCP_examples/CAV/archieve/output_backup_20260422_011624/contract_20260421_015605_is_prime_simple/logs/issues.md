# Contract Issues: is_prime_simple

No blocking issues.

Notes:

- The original interface is already verification-friendly: one scalar input, one scalar return, and no heap memory.
- The specification is written directly in `input/is_prime_simple.c`; no task-specific Coq bridge file is required.
- The contract intentionally contains no `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion.
