# Issues: remove_duplicates_sorted contract

## Resolved

- The output array suffix after the compressed prefix is intentionally unconstrained. The function's semantic result is the returned prefix length and prefix contents; later positions may contain old or overwritten values.
- A task-specific `.v` file is needed because the compressed-prefix list is most clearly expressed as a recursive Coq list function.

## Open

- None.
