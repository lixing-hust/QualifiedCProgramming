No blocking issues.

- Assumed the project uses the standard `INT_MIN` / `INT_MAX` macros from `verification_stdlib.h`, consistent with existing inputs.
- Chose a direct C-level postcondition instead of a custom Coq absolute-value definition because the function is simple and branch-free at the spec level.
