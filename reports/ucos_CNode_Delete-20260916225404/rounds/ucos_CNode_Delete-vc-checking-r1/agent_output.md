## Outcome

All three target witnesses can enter proving in one lightweight group, `delete-results`, with estimated difficulty 1. The three selected split proof routes were exercised successfully through the bound current-goal debug command; formal proofs and controller acceptance remain downstream responsibilities.

## Proof-Mode Decisions

The complete first pass found category split goal 1 provable, object split goal 1 provable, and unsupported split goal 1 provable. Only after this complete binary pass, all three parent witnesses were assigned `aggressive_pre_process`. Each parent has exactly one split goal, so no whole top-level provability analysis was required or performed.

## Common Proof Patterns

Pattern D evaluates the pure shared deletion transition. Unfold the selected split declaration before introducing its binders, then unfold `delete_slot_transition` and `delete_slot_result`. The proposition is equality between a returned integer/state pair and the concrete branch result. There are no remaining spatial resources, existential witnesses, frame transformations, or list obligations in these selected split targets. Concrete capability tags reduce directly; a symbolic unsupported tag requires elimination of its equality tests using the supplied disequalities. Finish the resulting pair/record equality by reflexivity. No new helper is needed, and no eligible prior sealed source was bound for reuse.

## VC Deltas

- `return_wit_1_category_cap`, split goal 1: Pattern D with old capability tag 1 and result 0. The new record has slot kind, capability kind, word0 and word1 equal to zero, with the old pointer preserved. All fields coincide by computation; address and integer-range premises are unused.
- `return_wit_2_object_cap`, split goal 1: Pattern D with old capability tag 2 and result 0. The new record has slot kind, capability kind, word0 and pointer equal to zero, with old word1 preserved. Again, computation establishes exact record equality.
- `return_wit_3_unsupported_cap`, split goal 1: Pattern D with symbolic old capability tag and result 9. `PreH4`/`PreH16` exclude tag 1 and `PreH3`/`PreH17` exclude tag 2. Destruct the two `Z.eq_dec` tests, reject their equality branches by contradiction, and preserve all five old state fields. These are already available premises, with no additional mathematical assumption.

## Grouping Decisions

Initial grouping placed all three return branches together because they evaluate the same shared transition and have identical pure record-equality context. The second review confirms three top-level witnesses, three small aggressive split goals, zero helper families, one shared model import, no mixed proof modes, and only final-return program phase. There is no separate transition/safety witness among the assigned targets to split away. The only slight tail is the unsupported branch's two elementary equality tests; it does not introduce heavy library or context load. Retaining this coherent group avoids unnecessary singleton scheduling and stays below both the preferred group size and the hard limit.

## Risks or Blockers

No annotation, specification, source, or dependency blocker was found. The final authorized debug invocation exited with code 0 and status `passed` after the concrete proof tactics for every selected split target. The exploratory script ends each goal with `Abort` as required and is not a formal proof artifact. Main-root C, generated sources, manual and case library were not modified.
