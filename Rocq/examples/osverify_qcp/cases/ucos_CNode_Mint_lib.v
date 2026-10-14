Require Export SimpleC.EE.osverify_qcp.cap_model.
Local Open Scope Z_scope.

(* The source is its PRE-state, including when source and destination alias.
   This is the sequential destination update in legacy MintPost', expressed
   over the same slot storage model as Grant and Delete. Index/null failures
   are handled before this transition by the C function contracts. *)
Definition mint_authorized (src : cap_slot_state) (rights : Z) : Prop :=
  cap_kind src = 1 /\
  Z.land (Z.lnot (cap_word1 src)) rights = 0 /\
  cap_word1 src <> rights.

Definition minted_slot (src dst : cap_slot_state) (rights : Z)
    : cap_slot_state :=
  Build_cap_slot_state (slot_kind dst) 1 (cap_word0 src) rights
    (cap_pointer dst).

Definition mint_slot_transition (src dst : cap_slot_state) (rights ret : Z)
    (out : cap_slot_state) : Prop :=
  (mint_authorized src rights /\ ret = 0 /\ out = minted_slot src dst rights) \/
  (~ mint_authorized src rights /\ ret = 5 /\ out = dst).

(* The three mutable capability words are the owned footprint. The destination
   tag and pointer, and the source tag and pointer, are arbitrary framed values.
   In the alias cases the C contract supplies the same PRE-state words for src
   and dst; no second spatial ownership is required by this pure relation. *)
Definition mint_cap_transition
    (ret rights src_kind src_word0 src_word1 dst_kind dst_word0 dst_word1
       new_kind new_word0 new_word1 : Z) : Prop :=
  forall src_tag src_ptr dst_tag dst_ptr,
    mint_slot_transition
      (Build_cap_slot_state src_tag src_kind src_word0 src_word1 src_ptr)
      (Build_cap_slot_state dst_tag dst_kind dst_word0 dst_word1 dst_ptr)
      rights ret
      (Build_cap_slot_state dst_tag new_kind new_word0 new_word1 dst_ptr).
