From Coq Require Export ZArith.
Local Open Scope Z_scope.

(* Sequential storage model shared by Grant and Delete.  The two union words
   and pointer each occur once.  This is not a legacy OSInv refinement. *)
Record cap_slot_state := {
  slot_kind : Z;
  cap_kind : Z;
  cap_word0 : Z;
  cap_word1 : Z;
  cap_pointer : Z
}.

Definition grant_slot_result (class right : Z) (s : cap_slot_state)
    : Z * cap_slot_state :=
  (0, Build_cap_slot_state (slot_kind s) 1 class
        (Z.lor (Z.land (cap_word1 s) 4095) right) (cap_pointer s)).

Definition delete_slot_result (s : cap_slot_state) : Z * cap_slot_state :=
  if Z.eq_dec (cap_kind s) 1 then
    (0, Build_cap_slot_state 0 0 0 0 (cap_pointer s))
  else if Z.eq_dec (cap_kind s) 2 then
    (0, Build_cap_slot_state 0 0 0 (cap_word1 s) 0)
  else (9, s).

(* Grant's local footprint omits slot_kind and pointer.  Quantifying those
   fields expresses preservation for any disjoint frame, not a guessed value. *)
Definition grant_cap_transition
    (ret class right old_cap old_word0 old_word1
         new_cap new_word0 new_word1 : Z) : Prop :=
  forall slot ptr,
    grant_slot_result class right
      (Build_cap_slot_state slot old_cap old_word0 old_word1 ptr) =
    (ret, Build_cap_slot_state slot new_cap new_word0 new_word1 ptr).

Definition delete_slot_transition
    (ret old_slot old_cap old_word0 old_word1 old_ptr
         new_slot new_cap new_word0 new_word1 new_ptr : Z) : Prop :=
  delete_slot_result
    (Build_cap_slot_state old_slot old_cap old_word0 old_word1 old_ptr) =
  (ret, Build_cap_slot_state new_slot new_cap new_word0 new_word1 new_ptr).
