# Contract issues: longest_increasing_run

No blocking issues.

Notes:

- A problem-specific Coq definition is needed because the result is a maximum over contiguous strictly increasing runs, not a simple existing scalar function.
- The original C interface is verification-friendly and was preserved.
- The generated C file intentionally contains no Verify-stage invariants or assertions.
