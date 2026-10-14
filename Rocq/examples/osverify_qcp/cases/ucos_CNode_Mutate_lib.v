Require Export SimpleC.EE.osverify_qcp.cap_model.
Local Open Scope Z_scope.

(* Sequential storage interpretation of the legacy Mutate guard and updates.
   The legacy whole-OS specification is not imported or claimed equivalent. *)
Definition mutate_authorized (src : cap_slot_state) (rights : Z) : Prop :=
  cap_kind src = 1 /\
  Z.land (Z.lnot (cap_word1 src)) rights = 0 /\
  cap_word1 src <> rights.

Definition mutate_destination (src dst : cap_slot_state) (rights : Z)
    : cap_slot_state :=
  Build_cap_slot_state (slot_kind dst) 1 (cap_word0 src) rights
    (cap_pointer dst).

Definition mutate_source (src : cap_slot_state) (rights : Z)
    : cap_slot_state :=
  Build_cap_slot_state 0 (cap_kind src) (cap_word0 src)
    (Z.land (cap_word1 src) (Z.lnot rights)) (cap_pointer src).

Definition mutate_distinct_transition (src dst : cap_slot_state) (rights ret : Z)
    (src_out dst_out : cap_slot_state) : Prop :=
  (mutate_authorized src rights /\ ret = 0 /\
    src_out = mutate_source src rights /\
    dst_out = mutate_destination src dst rights) \/
  (~mutate_authorized src rights /\ ret = 8 /\ src_out = src /\ dst_out = dst).

(* On aliasing, the source read-modify-write sees the just-written rights,
   not the original source rights. Its final slot tag and rights are zero. *)
Definition mutate_alias_transition (src : cap_slot_state) (rights ret : Z)
    (out : cap_slot_state) : Prop :=
  (mutate_authorized src rights /\ ret = 0 /\
    out = Build_cap_slot_state 0 1 (cap_word0 src) 0 (cap_pointer src)) \/
  (~mutate_authorized src rights /\ ret = 8 /\ out = src).

(* Flattened interfaces retain the original slot relations. Unwritten pointer
   fields and the destination tag are arbitrary framed values, quantified here
   rather than replaced with a guessed constant. *)
Definition mutate_alias_fields
    (ret rights old_tag old_kind word0 word1 new_tag new_kind
       new_word0 new_word1 : Z) : Prop :=
  forall ptr,
    mutate_alias_transition
      (Build_cap_slot_state old_tag old_kind word0 word1 ptr) rights ret
      (Build_cap_slot_state new_tag new_kind new_word0 new_word1 ptr).

Definition mutate_distinct_fields
    (ret rights src_tag src_kind src_word0 src_word1
       dst_kind dst_word0 dst_word1 new_src_tag new_src_word1
       new_dst_kind new_dst_word0 new_dst_word1 : Z) : Prop :=
  forall src_ptr dst_tag dst_ptr,
    mutate_distinct_transition
      (Build_cap_slot_state src_tag src_kind src_word0 src_word1 src_ptr)
      (Build_cap_slot_state dst_tag dst_kind dst_word0 dst_word1 dst_ptr)
      rights ret
      (Build_cap_slot_state new_src_tag src_kind src_word0 new_src_word1 src_ptr)
      (Build_cap_slot_state dst_tag new_dst_kind new_dst_word0 new_dst_word1 dst_ptr).
