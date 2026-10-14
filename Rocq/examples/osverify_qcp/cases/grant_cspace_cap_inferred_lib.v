(* First candidate, independently inferred from two bounded implementation bodies.
   No theorem or critical-primitive semantics is assumed here. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition grant_rights (old requested : Z) : Z :=
  Z.lor (Z.land old 4095) requested.
Definition grant_permit (running authorization parent current : Z) : Prop :=
  running = 0 \/ (Z.land authorization 64 <> 0 /\ parent = current).
Definition grant_permitb (running authorization parent current : Z) : bool :=
  Z.eqb running 0 || (negb (Z.eqb (Z.land authorization 64) 0) && Z.eqb parent current).
Definition grant_call_success (destination class destination_space : Z) : Prop :=
  0 <= class <= 16 /\ 0 <= destination < 64 /\ destination_space <> 0.
Definition grant_success (destination current_space running authorization parent current class destination_space : Z) : Prop :=
  0 <= destination < 63 /\ current_space <> 0 /\
  grant_permit running authorization parent current /\
  grant_call_success destination class destination_space.
Definition grant_return (destination current_space running authorization parent current class destination_space : Z) : Z :=
  if Z.leb 63 destination then 42 else
  if Z.eqb current_space 0 then 11 else
  if grant_permitb running authorization parent current then
    if Z.leb class 16 && negb (Z.eqb destination_space 0) then 0 else 11
  else 252.
Definition grant_call_return (destination class destination_space : Z) : Z :=
  if Z.leb 0 class && Z.leb class 16 && Z.ltb destination 64 &&
     negb (Z.eqb destination_space 0) then 0 else 11.

(* A mathematical observable partition, independent of implementation locals. *)
Definition grant_outcome (destination current_space running authorization parent current class destination_space old_priority new_priority result : Z) : Prop :=
  (63 <= destination /\ result = 42 /\ new_priority = old_priority) \/
  (0 <= destination < 63 /\ new_priority = current /\
    ((current_space = 0 /\ result = 11) \/
     (current_space <> 0 /\ ~ grant_permit running authorization parent current /\ result = 252) \/
     (current_space <> 0 /\ grant_permit running authorization parent current /\
      ((grant_call_success destination class destination_space /\ result = 0) \/
       (~ grant_call_success destination class destination_space /\ result = 11))))).

(* Cell names are physical addresses, so union aliases have one value.
   None permits a writable cell with unspecified/uninitialized old content.
   This relation says exactly which ordinary cells differ; primitive-state
   semantics is deliberately a separate unresolved obligation. *)
Definition grant_cell_update (before after : Z -> option Z)
    (type_address content_address right_address class requested old_right : Z) : Prop :=
  before right_address = Some old_right /\
  after type_address = Some 1 /\
  after content_address = Some class /\
  after right_address = Some (grant_rights old_right requested) /\
  (forall address, address <> type_address -> address <> content_address ->
     address <> right_address -> after address = before address).
Inductive grant_critical_event := GrantEnterCritical | GrantExitCritical.
Definition grant_primitive_trace (destination : Z) (events : list grant_critical_event) : Prop :=
  (63 <= destination /\ events = []) \/
  (0 <= destination < 63 /\ events = [GrantEnterCritical; GrantExitCritical]).

(* User-selected sequential ordinary-memory projection. These marker steps are
   DEFINED to be identity here. This is not a theorem about source encrit/excrit,
   interrupts, nesting or scheduling, and adds no axiom about those operations. *)
Definition grant_sequential_marker {Memory : Type}
    (_ : grant_critical_event) (ordinary_memory : Memory) : Memory := ordinary_memory.

(* A concrete conditional ownership interface for the actual callee. Addresses
   are the actual C lvalues supplied by annotation, never guessed layout offsets.
   It preserves invalid/null branches and permits uninitialized write-only cells. *)
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope sac.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
(* These pure constructors use the exact named address representation emitted
   for the current C lvalues; no numeric layout/union offsets are invented. *)
Definition grant_table_cell (destination : Z) : Z :=
  &( "OSCSpacePrioTbl" ) + destination * sizeof(PTR).
Definition grant_slot_cell (destination_space class : Z) : Z :=
  &((destination_space) # "cspace" ->ₛ "cnode" .ₛ "slots") + class * sizeof("slot").
Definition grant_type_cell (destination_space class : Z) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_dot_field (LE_arrow_field
      (RE_const (grant_slot_cell destination_space class) (FET_alias "slot"))
      "capability") "cap_type")).
Definition grant_category_cell (destination_space class : Z) (field : string) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_dot_field (LE_dot_field (LE_dot_field (LE_arrow_field
      (RE_const (grant_slot_cell destination_space class) (FET_alias "slot"))
      "capability") "cap_content") "category") field)).
Definition grant_call_pre (destination class destination_space old_right : Z) : Assertion :=
  if Z.leb class 16 then
    if Z.ltb destination 64 then
      grant_table_cell destination # Ptr |-> destination_space **
      (if Z.eqb destination_space 0 then emp else
        grant_type_cell destination_space class # UInt |->_ **
        grant_category_cell destination_space class "category_content" # UInt |->_ **
        grant_category_cell destination_space class "category_right" # UInt |-> old_right)
    else emp
  else emp.
