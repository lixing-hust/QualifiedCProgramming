# Contract Issues: array_scale

## Issues

None.

## Notes

- The raw prompt does not state integer overflow behavior. The generated contract adds the standard signed 32-bit multiplication safety precondition required for defined C `int` execution.
- No interface rewrite was needed.
- No task-specific Coq bridge file was needed.
