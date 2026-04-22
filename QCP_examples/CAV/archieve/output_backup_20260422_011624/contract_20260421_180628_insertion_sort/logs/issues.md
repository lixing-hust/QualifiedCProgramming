# Contract issues: insertion_sort

## Resolved

- The raw task's interface is already verification-friendly, so no interface rewrite was needed.
- Sorting semantics require both order and element preservation; the contract uses `sorted_z` plus Coq `Permutation`, matching existing local sort examples.
- A task-local `.v` file is needed because `sorted_z` is not a shared public definition in the C contract inputs.

## Open issues

- None for Contract.

## Deferred to Verify

- Proof annotations for sorted prefix, shifted segment, and element permutation preservation.
- Proof obligations for the inner loop's right shifts and final insertion step.
