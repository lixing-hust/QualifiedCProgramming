From Coq Require Import ZArith Bool.
Local Open Scope Z_scope.

(* Independent core-only spec. No OS model, prior case, or generated import. *)
Definition cd_input_domain (prio slot : Z) : Prop :=
  0 <= prio <= 255 /\ 0 <= slot <= 4294967295.

(* The observed pointer/type are irrelevant on paths that do not read them. *)
Definition cd_result (prio slot space old_type result : Z) : Prop :=
  ((255 <= slot \/ 64 <= prio) /\ result = 9) \/
  (slot < 255 /\ prio < 64 /\
    ((space = 0 /\ result = 9) \/
     (space <> 0 /\
       (((old_type = 1 \/ old_type = 2) /\ result = 0) \/
        (old_type <> 1 /\ old_type <> 2 /\ result = 9))))).

Definition cd_cap_type_after (old_type : Z) : Z :=
  if orb (Z.eqb old_type 1) (Z.eqb old_type 2) then 0 else old_type.

(* Full heap effects are the direct separating Require/Ensure in the C:
   category: cap_type, slot_type, word0 and word1 become zero;
   object: cap_type, slot_type, word0 and pointer become zero;
   unsupported type: only cap_type was read and is preserved.
   Unmentioned cells are framed, including the other union component.
   Writable payload/slot cells are not required to have initial values. *)
