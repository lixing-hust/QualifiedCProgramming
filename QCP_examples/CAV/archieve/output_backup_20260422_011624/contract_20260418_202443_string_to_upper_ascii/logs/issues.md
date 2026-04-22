# Contract Issues

## Summary

- Status: completed
- Blocking issues: none
- Interface rewrite required: no
- Task-local Coq helper required: yes

## Notes

- The raw problem statement gives a valid writable C string and in-place update semantics, so the original interface is already suitable for Contract output.
- The only nontrivial contract design choice is the post-state string value. A dedicated `.v` helper is required because the output is a pointwise transformed list, not a simple scalar predicate.
- As with other C-string scanning tasks in this repository, the contract must explicitly exclude interior terminators in the logical payload `l` so the scan length matches the modeled string length.
