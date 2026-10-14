Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import ios_int.
Require Import int_lock.
Require Import evt_spec_defs. 
Require Import ios_cap_defs.
Require Import abs_op.


(* We state the invariant that capability of child tasks never exceed
   that of parent tasks.
*)
(*cap1_right is subset of cap2_right*)
Definition cap_lesseq_slots (slot1 slot2: slot_val_type) :=
  match slot1 with
    | (slot1_type, (cap1_type, (cap1_content, cap1_right, obj1))) =>
    match slot2 with
      | (slot2_type, (cap2_type, (cap2_content, cap2_right, obj2))) =>
        Int.eq (Int.and (Int.not cap2_right) cap1_right) Int.zero = true
    end
  end.

Definition cap_lesseq_at_cap (O1: osabst) tid1 tid2 (cap: int32) :=
  exists acspace slots1 childs1 parent1 parent2 slots2 childs2 slot1 slot2,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace tid1 = Some (slots1, childs1, parent1) /\
    CSpaceMod.get acspace tid2 = Some (slots2, childs2, parent2) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) slots1 = Some slot1 /\
    nth_slots (Z.to_nat (Int.unsigned cap)) slots2 = Some slot2 /\
    cap_lesseq_slots slot1 slot2.

Definition cap_lesseq_all_caps (O1: osabst) tid1 tid2 :=
  forall cap,
    Int.lt cap Int.zero = false ->
    Int.lt cap (Int.repr OBJ_POSITION) = true ->
    cap_lesseq_at_cap O1 tid1 tid2 cap.

    

(*!here proof is not complete because nth_slots_update_nth_slots_same lemma
need some precondition*)
(* Now we show this property is preserved for each transition *)
Lemma cap_lesseq_at_cap_ucos_cnode_mint_succ:
  forall dest src cap rights rv O1 r O2 ,
    ucos_cnode_mint_succ
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: (Vint32 rights) :: rv :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_at_cap O2 dest src cap.
Proof.
  intros dest src cap rights rv O1 r O2 H neq.
  unfold ucos_cnode_mint_succ in H.
  do 6 destruct H.
  inverts H. 
  destruct H0. do 16 destruct H.
  destruct H.  
  destruct H0 as [H01 [H02 [H03 [H04 [H05 [H06 [H07 [H08 H09]]]]]]]].
  destruct H09 as [H10|H11].
  {
    destruct H10 as [H10a H10b].
    inversion H10b.
    unfold cap_lesseq_at_cap.
    repeat eexists.
    rewrite get_set_eq. auto.
    rewrite CSpaceMod.map_get_set. auto.
    rewrite CSpaceMod.map_get_set'. rewrite H01. auto.
    auto.
    rewrite nth_slots_update_nth_slots_same. auto.
    rewrite H04. auto.
    unfold cap_lesseq_slots. auto.
  }
  {
    destruct H10 as [H10 H10b]. tryfalse.
  }
Qed.

Lemma cap_lesseq_all_caps_ucos_cnode_mint_succ:
  forall dest src cap rights O1 r O2,
    ucos_cnode_mint_succ
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: (Vint32 rights) :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_all_caps O1 dest src ->
    cap_lesseq_all_caps O2 dest src.
Proof.
  intros dest src cap rights O1 r O2 H neq Hprev.
  unfold cap_lesseq_all_caps.
  intros cap0 cap0_zero cap0_obj_pos.
  unfold cap_lesseq_all_caps in Hprev.
  lets Hprev2: Hprev cap0 cap0_zero cap0_obj_pos.
Admitted.

Lemma cap_lesseq_at_cap_ucos_cnode_copy_category_succ:
  forall dest src cap rv O1 r O2,
    ucos_cnode_copy_category_succ
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: rv :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_at_cap O2 dest src cap.
Proof.
  intros dest src cap rv O1 r O2 H neq.
  unfold ucos_cnode_copy_category_succ in H.
  destruct H as [H H0].
  destruct H0 as [dest1 [src1 [cap1 H0]]].
  destruct H0 as [eqs H0].
  inversion eqs.
  destruct H0 as [acspace [src_slots [src_childs [dest_slots [dest_childs H0]]]]].
  destruct H0 as [src_slot_type [src_cap_type [src_cap_content [src_cap_right [src_object_t H0]]]]].
  destruct H0 as [dest_slot_type [dest_cap_type [dest_cap_content [dest_cap_right [dest_object_t H0]]]]].
  destruct H0 as [H01 [H02 [H03 [H04 [H05 [H06 [H07 H08]]]]]]].
  destruct H08 as [H08|H08].
  {
    destruct H08 as [H08a H08b].
    inversion H08b.
    unfold cap_lesseq_at_cap.
    repeat eexists.
    rewrite get_set_eq. auto.
    rewrite CSpaceMod.map_get_set. auto.
    rewrite CSpaceMod.map_get_set'. rewrite H02. auto.
      rewrite <- H2. rewrite <- H3. apply neq.
    rewrite nth_slots_update_nth_slots_same. auto.
    rewrite H04. auto.
    unfold cap_lesseq_slots.
    clear - H06.
    Check Int.and_not_self.
    admit.
  }
  {
    destruct H08 as [H08a H08b].
    tryfalse.
  }
Admitted.

Lemma cap_lesseq_all_caps_ucos_cnode_copy_category_succ:
  forall dest src cap O1 r O2,
    ucos_cnode_copy_category_succ
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_all_caps O1 dest src ->
    cap_lesseq_all_caps O2 dest src.
Proof.
  intros dest src cap O1 r O2 H neq Hprev.
  unfold cap_lesseq_all_caps.
  intros cap0 cap0_zero cap0_obj_pos.
  unfold cap_lesseq_all_caps in Hprev.
  lets Hprev2: Hprev cap0 cap0_zero cap0_obj_pos.
Admitted.

(* This function describes the location of object copy.

   ucos_cnode_copy_object_dest_cap O1 dest src cap dest_idx
   means starting from abstract state O1, copy the object capability
   at location cap from src to dest updates the object capability
   at location dest_idx.
*)
Inductive ucos_cnode_copy_object_dest_cap:
  osabst -> int32 -> int32 -> int32 -> int32 -> Prop :=
| ucos_cnode_copy_object_dest_cap1:
  forall (O1: osabst) acspace dest src cap src_slots src_childs dest_slots dest_childs,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  forall dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
    get O1 cspaceid = Some (capcspace acspace) ->
    CSpaceMod.get acspace src = Some (src_slots, src_childs) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, src_object_t))) ->
    ucos_cnode_copy_object_dest_cap O1 dest src cap dest_idx
| ucos_cnode_copy_object_dest_cap2:
  forall (O1: osabst) acspace dest src cap src_slots src_childs dest_slots dest_childs,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
    get O1 cspaceid = Some (capcspace acspace) ->
    CSpaceMod.get acspace src = Some (src_slots, src_childs) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    (~exists dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
    nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, src_object_t)))) ->
    ucos_cnode_copy_object_dest_cap O1 dest src cap (Int.repr (Z.of_nat (length dest_slots))).

(* Capability of slot1 is at most capability of slot2 on the same object. *)
Definition cap_lesseq_obj_slot (slot1 slot2: slot_val_type) :=
  match slot1 with
    | (slot1_type, (cap1_type, (cap1_content, cap1_right, obj1))) =>
    match slot2 with
      | (slot2_type, (cap2_type, (cap2_content, cap2_right, obj2))) =>
        Int.lt cap2_right cap1_right = false /\
        obj1 = obj2
    end
  end.

(* Capability of tid1 is at most capability of tid2.
   
   Here cap corresponds to the index of some object capability in
   tid1. There must exist some cap location in tid2 *)
Definition cap_lesseq_obj_at_cap (O1: osabst) tid1 tid2 (cap: int32) :=
  exists acspace slots1 childs1 slots2 childs2 slot1 cap2 slot2,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace tid1 = Some (slots1, childs1) /\
    CSpaceMod.get acspace tid2 = Some (slots2, childs2) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) slots1 = Some slot1 /\
    nth_slots (Z.to_nat (Int.unsigned cap2)) slots2 = Some slot2 /\
    cap_lesseq_obj_slot slot1 slot2.

(* Capability of tid1 is at most capability of tid2 on all objects. *)
Definition cap_lesseq_obj_all_caps (O1: osabst) tid1 tid2 :=
  exists acspace slots childs,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace tid1 = Some (slots, childs) /\
    forall cap,
      Int.lt cap (Int.repr OBJ_POSITION) = false ->
      Int.lt cap (Int.repr (Z.of_nat (length slots))) = true ->
      cap_lesseq_obj_at_cap O1 tid1 tid2 cap.

Lemma cap_lesseq_obj_at_cap_ucos_cnode_copy_object_succ1:
  forall dest src cap O1 r O2 dest_idx,
    ucos_cnode_copy_object_succ1
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    ucos_cnode_copy_object_dest_cap O1 dest src cap dest_idx ->
    cap_lesseq_obj_at_cap O2 dest src dest_idx.
Proof.
Admitted.

Lemma cap_lesseq_obj_at_cap_ucos_cnode_copy_object_succ2:
  forall dest src cap O1 r O2 dest_idx,
    ucos_cnode_copy_object_succ2
    ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: nil)
    O1 (Some r, Some O2) ->
  dest <> src ->
  ucos_cnode_copy_object_dest_cap O1 dest src cap dest_idx ->
  cap_lesseq_obj_at_cap O2 dest src dest_idx.
Proof.
Admitted.

Lemma cap_lesseq_obj_all_caps_ucos_cnode_copy_object_succ1:
  forall dest src cap O1 r O2,
    ucos_cnode_copy_object_succ1
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_obj_all_caps O1 dest src ->
    cap_lesseq_obj_all_caps O2 dest src.
Proof.
Admitted.

Lemma cap_lesseq_obj_all_caps_ucos_cnode_copy_object_succ2:
  forall dest src cap O1 r O2,
    ucos_cnode_copy_object_succ2
      ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: nil)
      O1 (Some r, Some O2) ->
    dest <> src ->
    cap_lesseq_obj_all_caps O1 dest src ->
    cap_lesseq_obj_all_caps O2 dest src.
Proof.
Admitted.

Inductive has_cur_prio: osabst -> int32 -> Prop :=
| has_cur_prio_rule:
  forall O1 t tls prio st msg sus,
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (prio, st, msg, sus) ->
    has_cur_prio O1 prio.
