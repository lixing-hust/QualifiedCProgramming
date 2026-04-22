# Contract Reasoning

## Source Semantics

Target function: `array_move_zeroes_to_end`.

The function mutates the input array in place. The first loop scans indices `0..n-1` and writes every nonzero value to the next available prefix position, preserving scan order. The second loop fills every remaining position from `write` to `n-1` with `0`.

For `n == 0`, both loops are skipped and the empty array remains empty.

## Mathematical Model

The result list is:

- all nonzero elements of the original list, in their original relative order;
- followed by exactly the original zero elements, represented as zero values.

This is encoded by the Coq helper:

- `move_zeroes_nonzeroes l`: filters out zero values and preserves nonzero order;
- `move_zeroes_zeroes l`: keeps one `0` for each zero in the original list;
- `move_zeroes_to_end_spec l`: appends those two lists.

This topic-specific list function is clearer and more reusable than expanding the full pointwise prefix/suffix relation directly in the C postcondition.

## Preconditions

The contract requires:

- `0 <= n`, matching the problem statement;
- `Zlength(l) == n`, tying the logical list to the physical array length;
- `IntArray::full(a, n, l)`, giving read/write ownership of the whole array.

No extra element-range constraints are needed. The function only copies existing `int` values and writes literal `0`; it performs no arithmetic on element values. Loop counters are `int` locals bounded by `n`.

## Postcondition

The postcondition returns the same array ownership at the same address and length, with contents `move_zeroes_to_end_spec(l)`.

The contract intentionally does not include loop invariants, assertions, bridge assertions, or exit assertions. Those belong to the Verify stage.

## Coq Dependency Decision

An `input/array_move_zeroes_to_end.v` file is needed because the natural specification is a topic-specific list transformation. There is no simple existing public function name in the C contract language that expresses stable nonzero filtering followed by zero padding.
