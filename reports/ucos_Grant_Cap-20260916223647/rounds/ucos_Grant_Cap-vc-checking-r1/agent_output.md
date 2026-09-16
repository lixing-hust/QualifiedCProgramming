## Outcome

Ready for proving: one top-level witness, two generated split goals, one light group (`grant-result`). No new helper is needed. The sole group is the expected critical path.

## Proof-Mode Decisions

In manual declaration order, `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1` is provable, and `proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial` is provable. Both binary decisions were completed before selecting a mode. Their parent `proof_of_ucos_Grant_Cap_return_wit_1_valid_target` therefore uses `aggressive_pre_process`; no whole-goal provability analysis was performed.

## Common Proof Patterns

P1 — Definitional transition: after introducing generated binders, establish the pure right-hand assertion independently of the owned heap. Unfold the transition and its slot operation, introduce the universally quantified preserved slot-kind and pointer, and reduce record projections to reflexivity.

P2 — Equal-name frame: substitute the equal program/pre-state names and cancel matching points-to resources modulo separation associativity and commutativity. No heap value, address, or existential witness changes.

## VC Deltas

The selected semantic split uses P1. The left side owns category-right, category-content, cap-type, and the destination table entry. The right side is the pure `grant_cap_transition` for return 0 and new type/content/right values `1`, `cap_Class_pre`, and `Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre`. Controller debug expansion of `grant_cap_transition` and `grant_slot_result` yields equal pairs containing records; old type/content disappear, while arbitrary slot-kind and pointer are preserved by record projections. There are no existential choices, additional arithmetic requirements, or missing helper premises.

The spatial split uses P2. `PreH11`, `PreH12`, and `PreH13` identify the destination, class, and right names, respectively. They make all four right-hand resources identical to the left-hand resources: the same destination-table pointer and the same slot's type 1, content equal to class, and masked/combined right. Only their order differs. The bounds and non-null premises require no additional use for this entailment.

No sealed previous source is bound, so proof reuse comparison was skipped and no reuse hints were created.

## Grouping Decisions

The initial grouping places the single return witness and its two splits together. The independent second review confirms one top-level witness, two light aggressive splits, zero helper families, one shared slot-model definition, and ordinary separation cancellation. There is no mixed mode, loop context, or substantial library burden. A single-witness group is required because the entire manual target set is this one final-result obligation; its splits cannot be assigned separately. No independent transition/safety top-level target remains to split from the final result. Difficulty is 1, and the sole group's small, indivisible workload is the critical path.

## Risks or Blockers

None found. The final declared debug script covers exactly the two selected split goals and the controller debug command exited 0 with status `passed`. This establishes inspection success; controller plan acceptance and group proof checks remain separate.
