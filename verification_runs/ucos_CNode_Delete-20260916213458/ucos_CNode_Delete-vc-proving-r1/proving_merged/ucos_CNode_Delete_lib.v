From Coq Require Import ZArith.
Local Open Scope Z_scope.

(* Logical slot state in storage order. The union overlays its first two
   integer fields; the last field is a pointer represented in QCP by Z.
   This captures the sequential slot update in the legacy DeletePost'. *)
Record delete_slot_state := {
  delete_slot_kind : Z;
  delete_cap_kind : Z;
  delete_word0 : Z;
  delete_word1 : Z;
  delete_object : Z
}.

Definition delete_slot_result (s : delete_slot_state) : Z * delete_slot_state :=
  if Z.eq_dec (delete_cap_kind s) 1 then
    (0, Build_delete_slot_state 0 0 0 0 (delete_object s))
  else if Z.eq_dec (delete_cap_kind s) 2 then
    (0, Build_delete_slot_state 0 0 0 (delete_word1 s) 0)
  else (9, s).

(* Flat annotation interface to the complete slot transition.  Each argument
   denotes a storage value, not an independently owned union member. *)
Definition delete_slot_transition
    (ret old_slot old_cap old_word0 old_word1 old_ptr
         new_slot new_cap new_word0 new_word1 new_ptr : Z) : Prop :=
  delete_slot_result
    (Build_delete_slot_state old_slot old_cap old_word0 old_word1 old_ptr) =
  (ret, Build_delete_slot_state new_slot new_cap new_word0 new_word1 new_ptr).
