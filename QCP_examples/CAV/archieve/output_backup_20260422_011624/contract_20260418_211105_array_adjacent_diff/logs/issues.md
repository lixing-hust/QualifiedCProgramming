No blocking issues.

- The contract assumes `IntArray::full` supports zero-length arrays for the `n == 1` case, consistent with existing repository usage on `0 <= n` array tasks.
- No interface rewrite was necessary.
- No extra Coq definitions were necessary.
