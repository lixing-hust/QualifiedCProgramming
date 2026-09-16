# Shared grant contract review

The current C implementation selects the four contracts from the sole shared declaration. Class-invalid and priority-invalid inputs return 11 without heap access; null-target inputs return 11 preserving the table entry; valid-target inputs preserve the table entry and update precisely cap_type, category_content and category_right. The final rights value is `(old_right & 4095) | right`.

The existing case lib exports the shared cap_model and needs no local replacement. The shared grant_cap_transition has nine Z arguments in the same order as the header's Extern Coq declaration. It relates the old and new slot fields through grant_slot_result and universally preserves arbitrary slot-kind/pointer frame values. This flat final-state relation is appropriate for the requested sequential abstraction; no loop interpreter, extra axiom or generated import is needed. The guarantee does not assert legacy OSInv refinement or concurrency correctness.

The predicate-first positive majority-element example and algorithm-mirror negative example were reviewed as design contrasts. This case has no loop, higher-order existential witness, explicit branch-control command or ordinary Assert. Ordinary Assert review: none.

# Include repair and checks

The exact handoff symexec exits 1 before invoking symbolic execution. Its first_failure has category `tool`, kind `annotation-main-symexec-invocation`, and message:

> quoted include must stay under QCP_examples: '../include/ucos_Grant_Cap_spec.h' from /home/lixing/projects/QualifiedCProgramming/QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c

The controller reported generated_refresh `rolled-back`; returncode was null. A read-only realpath check resolved the include inside QCP_examples. Main then identified the controller's collection-root include convention and explicitly directed the local integration repair: change the target C include to `include/ucos_Grant_Cap_spec.h`. This still selects the same shared declaration and changes no executable statement or contract.

The first formal-case-lib command also exited 1 because a current generated source_goal_version was unavailable. After the include repair, the unchanged exact symexec completed with `status: passed`, exit 0, and committed all four generated roles. The unchanged exact formal-case-lib check then completed with `status: passed`, exit 0.

Annotation-checking was bracketed by the exact timing start/finish commands after these checks passed. The generated goal contains all four return cases, 14 safety witnesses and 5 partial-solve witnesses. Its valid-target return explicitly retains grant_cap_transition with the current class/right values and the final field stores; entry equalities connect them to the contract variables. The manual has one unresolved top-level valid-target return witness with a pure transition split and a spatial split. These are proof obligations, not missing annotation premises. The auto file contains generated proof seeds and is left exclusively to the controller workflow; no completed whole-case proof is claimed here.

Only the explicitly authorized target include spelling was manually changed. The case lib and shared inputs are unchanged, and generated roles were refreshed solely by controller symexec. No additional Assert, contract duplication, spec weakening or executable change was needed. The current candidate is ready for main-owned finalize and acceptance.
