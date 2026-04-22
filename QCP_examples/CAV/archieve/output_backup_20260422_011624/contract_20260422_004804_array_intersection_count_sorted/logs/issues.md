# Contract issues: array_intersection_count_sorted

## Issue 1: no public multiset-intersection-count function

- Trigger: the postcondition needs the exact multiplicity-aware intersection size of two sorted lists.
- Decision: added `input/array_intersection_count_sorted.v` with a single topic-specific recursive function.
- Scope: no public experience document needed an update.

## Issue 2: overflow boundary for `count++`

- Trigger: the loop increments `count` once per successful pair.
- Decision: require `0 <= n <= INT_MAX` and `0 <= m <= INT_MAX`; Verify-stage invariants can use the fact that successful pairs are bounded by the consumed prefixes and ultimately by both lengths.
- Scope: no implementation rewrite was needed.
