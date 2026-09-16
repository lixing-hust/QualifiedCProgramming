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
