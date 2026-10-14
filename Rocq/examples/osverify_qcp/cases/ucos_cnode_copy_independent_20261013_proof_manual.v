Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_cnode_copy_independent_20261013_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_cnode_copy_independent_20261013_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_get_obj_slot_copy_independent_20261013_lib.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_copy_independent_20261013_lib.
Local Open Scope sac.

Lemma proof_of_ucos_CNode_Copy_entail_wit_1_split_goal_spatial : ucos_CNode_Copy_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  destruct PreH7 as [_ [ND [_ [RD _]]]].
  destruct (RD PreH3 PreH2 PreH1) as [D S].
  rewrite Z.mul_comm.
  apply (copy_read_focus__access h _ true _ ND D).
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_1 : ucos_CNode_Copy_entail_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_ucos_CNode_Copy_entail_wit_1_split_goal_spatial. Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_2_split_goal_spatial : ucos_CNode_Copy_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH4 as [_ [ND [_ [RD _]]]].
  destruct (RD PreH1 PreH2 PreH3) as [D S].
  replace (d0 * sizeof(PTR)) with (sizeof(PTR) * d0) by ring.
  replace (s0 * sizeof(PTR)) with (sizeof(PTR) * s0) by ring.
  sep_apply_l_atomic (copy_read_restore__access h _ true _ ND D).
  apply (copy_read_focus__access h _ true _ ND S).
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_2 : ucos_CNode_Copy_entail_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_ucos_CNode_Copy_entail_wit_2_split_goal_spatial. Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_3_split_goal_spatial : ucos_CNode_Copy_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; subst; repeat split; assumption).
  destruct PreH6 as [_ [ND [_ [RD [RT _]]]]].
  destruct (RD PreH3 PreH4 PreH5) as [D S].
  specialize (RT LIVE).
  replace (s0 * sizeof(PTR)) with (sizeof(PTR) * s0) by ring.
  sep_apply_l_atomic (copy_read_restore__access h _ true _ ND S).
  apply (copy_read_focus__access h _ false _ ND RT).
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_3 : ucos_CNode_Copy_entail_wit_3.
Proof. aggressive_pre_process. Goal_apply proof_of_ucos_CNode_Copy_entail_wit_3_split_goal_spatial. Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_4 : ucos_CNode_Copy_entail_wit_4.
Proof.
 LLM_pre_process ltac:(lia).
 assert (Hl : copy_live a d0 s0 f0) by (unfold copy_live; subst; tauto).
 pose proof PreH5 as Hp.
 destruct Hp as [_ [Hnd [_ [_ [Hs [Hcat _]]]]]].
 specialize (Hs Hl). specialize (Hcat Hl PreH1).
 destruct Hcat as [_ [_ [[v Hd] _]]].
 split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
 subst pCSpace1 pCSpace2 cap1 cap2.
 unfold copy_tag_address, copy_slot_lvalue in Hs, Hd.
 cbn zeta in Hs, Hd.
 revert Hs Hd. csimpl. intros Hs Hd.
 pose proof (copy_heap_focus__category_steps h _ Hnd Hs) as [_ Hr].
 cbn [copy_cell_addr copy_cell_heap copy_cell_ptr copy_cell_value] in Hr.
 sep_apply_l_atomic Hr.
 pose proof (copy_heap_focus__category_steps h _ Hnd Hd) as [Hdex _].
 sep_apply_l_atomic Hdex.
 destruct v as [v|]; cbn [copy_cell_heap copy_cell_addr copy_cell_ptr copy_cell_value].
 - sep_apply store_uint_undef_store_uint. cancel.
 - cancel.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_5 : ucos_CNode_Copy_entail_wit_5.
Proof.
 LLM_pre_process ltac:(lia).
 assert (Hl : copy_live a d0 s0 f0) by (unfold copy_live; subst; tauto).
 pose proof PreH4 as Hp.
 destruct Hp as [_ [Hnd [_ [_ [_ [Hcat _]]]]]].
 specialize (Hcat Hl PreH11).
 destruct Hcat as [Hs0 [_ [Ht [Hd0 _]]]].
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 0 1 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hts.
 cbn [copy_component_address] in Hts.
 pose proof (copy_put_read__category_steps _ _ 1 _ _ _ Hts Hs0) as Hrs.
 pose proof (copy_put_writable__category_steps h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1 _ _ Hd0) as Hwd.
 assert (Hnp : NoDup (map copy_cell_addr (copy_put h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1))) by (rewrite copy_put_preserves__category_steps; exact Hnd).
 assert (Et : &((cap1) # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") f0).
 { subst; unfold copy_tag_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Ed : &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Es : &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a s0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 destruct (Z.eq_dec &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) as [E|E].
 - Left. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   rewrite Et, Es.
   sep_apply_l_atomic (copy_restore_uint__category_steps _ _ 1 Hnd Ht).
   apply copy_heap_read__category_steps; assumption.
 - Right. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   rewrite Et, Ed, Es. rewrite Ed, Es in E.
   sep_apply_l_atomic (copy_restore_uint__category_steps _ _ 1 Hnd Ht).
   sep_apply_l_atomic (copy_heap_two_focus__category_steps _ _ _ _ Hnp E Hwd Hrs).
   match goal with |- context [copy_two_holes ?hh ?xx ?yy] => cancel (copy_two_holes hh xx yy) end. cancel.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_6_1 : ucos_CNode_Copy_entail_wit_6_1.
Proof.
 LLM_pre_process ltac:(lia).
 assert (Hl : copy_live a d0 s0 f0) by (unfold copy_live; subst; tauto).
 pose proof PreH4 as Hp.
 destruct Hp as [_ [Hnd [_ [_ [_ [Hcat _]]]]]].
 specialize (Hcat Hl PreH11).
 destruct Hcat as [Hs0 [Hs1 [Ht [Hd0 Hd1]]]].
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 0 1 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hts0.
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 0 2 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hts1.
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 1 2 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hds1.
 pose proof (copy_put_read__category_steps _ _ 1 _ _ _ Hts0 Hs0) as Hrs0.
 pose proof (copy_put_read__category_steps _ _ 1 _ _ _ Hts1 Hs1) as Hr1.
 pose proof (copy_put_read__category_steps _ _ (copy_word0 (copy_slots a (copy_table a s0) f0)) _ _ _ Hds1 Hr1) as Hrs1.
 pose proof (copy_put_writable__category_steps h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1 _ _ Hd0) as Hwd0.
 pose proof (copy_put_writable__category_steps h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1 _ _ Hd1) as Hw1.
 pose proof (copy_put_writable__category_steps _ (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content") (copy_word0 (copy_slots a (copy_table a s0) f0)) _ _ Hw1) as Hwd1.
 assert (Hnp : NoDup (map copy_cell_addr (copy_put h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1))) by (rewrite copy_put_preserves__category_steps; exact Hnd).
 assert (Hnpp : NoDup (map copy_cell_addr (copy_put (copy_put h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1) (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content") (copy_word0 (copy_slots a (copy_table a s0) f0))))) by (rewrite copy_put_preserves__category_steps; exact Hnp).
 assert (Et : &((cap1) # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") f0).
 { subst; unfold copy_tag_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Ed0 : &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Es0 : &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a s0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Ed1 : &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = copy_category_address (copy_table a d0) sizeof("slot") f0 "category_right").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Es1 : &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = copy_category_address (copy_table a s0) sizeof("slot") f0 "category_right").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 rewrite Et, Ed0, Es0, Ed1, Es1.
 rewrite Ed0, Es0 in PreH12.
 rewrite <- PreH12.
 sep_apply_l_atomic (copy_restore_uint__category_steps _ _ (copy_word0 (copy_slots a (copy_table a s0) f0)) Hnp Hwd0).
 destruct (Z.eq_dec (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_right") (copy_category_address (copy_table a s0) sizeof("slot") f0 "category_right")) as [E|E].
 - Left. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   apply copy_heap_read__category_steps; assumption.
 - Right. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   sep_apply_l_atomic (copy_heap_two_focus__category_steps _ _ _ _ Hnpp E Hwd1 Hrs1).
   match goal with |- context [copy_two_holes ?hh ?xx ?yy] => cancel (copy_two_holes hh xx yy) end. cancel.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_6_2 : ucos_CNode_Copy_entail_wit_6_2.
Proof.
 LLM_pre_process ltac:(lia).
 assert (Hl : copy_live a d0 s0 f0) by (unfold copy_live; subst; tauto).
 pose proof PreH4 as Hp.
 destruct Hp as [_ [Hnd [_ [_ [_ [Hcat _]]]]]].
 specialize (Hcat Hl PreH11).
 destruct Hcat as [Hs0 [Hs1 [Ht [Hd0 Hd1]]]].
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 0 1 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hts0.
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 0 2 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hts1.
 pose proof (copy_layout_separation__category_steps h a _ _ _ _ d0 s0 f0 (copy_table a d0) (copy_table a s0) 1 2 PreH4 Hl (or_introl eq_refl) (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as Hds1.
 pose proof (copy_put_read__category_steps _ _ 1 _ _ _ Hts0 Hs0) as Hrs0.
 pose proof (copy_put_read__category_steps _ _ 1 _ _ _ Hts1 Hs1) as Hr1.
 pose proof (copy_put_read__category_steps _ _ (copy_word0 (copy_slots a (copy_table a s0) f0)) _ _ _ Hds1 Hr1) as Hrs1.
 pose proof (copy_put_writable__category_steps h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1 _ _ Hd0) as Hwd0.
 pose proof (copy_put_writable__category_steps h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1 _ _ Hd1) as Hw1.
 pose proof (copy_put_writable__category_steps _ (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content") (copy_word0 (copy_slots a (copy_table a s0) f0)) _ _ Hw1) as Hwd1.
 assert (Hnp : NoDup (map copy_cell_addr (copy_put h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1))) by (rewrite copy_put_preserves__category_steps; exact Hnd).
 assert (Hnpp : NoDup (map copy_cell_addr (copy_put (copy_put h (copy_tag_address (copy_table a d0) sizeof("slot") f0) 1) (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content") (copy_word0 (copy_slots a (copy_table a s0) f0))))) by (rewrite copy_put_preserves__category_steps; exact Hnp).
 assert (Et : &((cap1) # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") f0).
 { subst; unfold copy_tag_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Ed0 : &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a d0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Es0 : &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = copy_category_address (copy_table a s0) sizeof("slot") f0 "category_content").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Ed1 : &((cap1) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = copy_category_address (copy_table a d0) sizeof("slot") f0 "category_right").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 assert (Es1 : &((cap2) # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = copy_category_address (copy_table a s0) sizeof("slot") f0 "category_right").
 { subst; unfold copy_category_address, copy_slot_lvalue; cbn zeta; csimpl; reflexivity. }
 rewrite Et, Ed0, Es0, Ed1, Es1.
 rewrite Ed0, Es0 in PreH12.
 sep_apply_l_atomic (copy_two_restore__category_steps _ _ _ _ (copy_word0 (copy_slots a (copy_table a s0) f0)) Hnp PreH12 Hwd0 Hrs0).
 destruct (Z.eq_dec (copy_category_address (copy_table a d0) sizeof("slot") f0 "category_right") (copy_category_address (copy_table a s0) sizeof("slot") f0 "category_right")) as [E|E].
 - Left. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   apply copy_heap_read__category_steps; assumption.
 - Right. split_pure_spatial; [|split_pures; dump_pre_spatial; auto].
   sep_apply_l_atomic (copy_heap_two_focus__category_steps _ _ _ _ Hnpp E Hwd1 Hrs1).
   match goal with |- context [copy_two_holes ?hh ?xx ?yy] => cancel (copy_two_holes hh xx yy) end. cancel.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_7_split_goal_spatial : ucos_CNode_Copy_entail_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; subst; repeat split; assumption).
  destruct PreH8 as [_ [ND [_ [_ [RT [_ RO]]]]]].
  specialize (RT LIVE). destruct (RO LIVE PreH3) as [RP _].
  subst pCSpace1 pCSpace2 cap1 cap2.
  rewrite copy_tag_cap_address__access in RT.
  rewrite copy_object_cap_address__access in RP.
  sep_apply_l_atomic (copy_read_restore__access h _ false _ ND RT).
  apply (copy_read_focus__access h _ true _ ND RP).
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_7 : ucos_CNode_Copy_entail_wit_7.
Proof. aggressive_pre_process. Goal_apply proof_of_ucos_CNode_Copy_entail_wit_7_split_goal_spatial. Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_8 : ucos_CNode_Copy_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pCSpace1 pCSpace2 cap1 cap2.
  assert (Hlive : copy_live a d0 s0 f0) by (unfold copy_live; auto).
  pose proof PreH4 as [Hsafe [Hnd [Hlayout [Htabs [Htagread [Hcat Hobj]]]]]].
  pose proof (proj1 (proj1 Hsafe)) as Hdrange.
  specialize (Hobj Hlive PreH11). destruct Hobj as [Hsrc [Hscan Hwrite]].
  match goal with |- context [copy_hole h ?addr] =>
    assert (Haddr : addr = copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t")
      by (unfold copy_object_address, copy_slot_lvalue; csimpl; reflexivity);
    rewrite Haddr
  end.
  sep_apply_l_atomic (copy_heap_ptr_restore__lookup h
    (copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t")
    (copy_pointer (copy_slots a (copy_table a s0) f0)) Hnd Hsrc).
  destruct (Z_lt_dec d0 63) as [Hd|Hd].
  - pose proof (proj1 (Hscan Hd)) as Hcounter.
    prop_apply_p (copy_heap_uint_range__lookup h (&("OSCSpaceObjectPointer")+4*d0) (copy_counter a d0) Hnd Hcounter).
    Intros_p Hrange.
    destruct (copy_lookup_prefix__lookup _ _ _ _ _ _ _ _ _ PreH4 Hlive PreH11 Hd Hrange)
      as [xs [Hag [Hinput Hrecords]]].
    pose proof Hinput as [_ Hreadsafe]. specialize (Hreadsafe Hd PreH7).
    destruct Hreadsafe as [_ [Hlen _]]. unfold copy_lookup_count in Hlen.
    Exists xs. split_pure_spatial.
    + unfold copy_call_rest. destruct (Z_lt_dec d0 63); [|lia].
      sep_apply_l_atomic (proj1 (copy_lookup_partition__lookup _ _ _ _ _ _ _ _ _ xs PreH4 Hlive Hd Hlen Hrecords)).
      sep_apply_r_atomic (proj2 (copy_resources_active__lookup &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) (copy_counter a d0) xs Hd PreH7)).
      cancel (copy_call_frame h &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) xs).
      cancel (copy_lookup_cells (copy_table a d0) sizeof("slot") 17 xs); cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - assert (Hag : copy_lookup_agrees a d0 (@nil Z)).
    { intros j Hj. change (17 <= j < 17) in Hj; lia. }
    assert (Hinput : copy_lookup_input_safe d0 (copy_table a d0) (copy_counter a d0)
      (copy_pointer (copy_slots a (copy_table a s0) f0)) (@nil Z)).
    { split; [exact Hdrange|]. intros Hlt; lia. }
    assert (Hrecords : copy_call_records h &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) (copy_counter a d0) (@nil Z)) by (intro Hlt; lia).
    Exists (@nil Z). split_pure_spatial.
    + unfold copy_call_rest. destruct (Z_lt_dec d0 63); [lia|].
      sep_apply_r_atomic (proj2 (copy_resources_sentinel__lookup &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) (copy_counter a d0) (@nil Z) ltac:(lia))).
      cancel (copy_heap h); cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_9_split_goal_1 : ucos_CNode_Copy_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst pCSpace1. eapply copy_lookup_refines__lookup; eauto.
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_9_split_goal_spatial : ucos_CNode_Copy_entail_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pCSpace1 pCSpace2.
  assert (Hlive : copy_live a d0 s0 f0) by (unfold copy_live; auto).
  unfold copy_call_rest. destruct (Z_lt_dec d0 63) as [Hd|Hd].
  - destruct PreH17 as [_ Hsafe]. specialize (Hsafe Hd PreH8).
    destruct Hsafe as [_ [Hlen _]]. unfold copy_lookup_count in Hlen.
    sep_apply_l_atomic (proj1 (copy_resources_active__lookup &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) (copy_counter a d0) xs Hd PreH8)).
    sep_apply_r_atomic (proj2 (copy_lookup_partition__lookup _ _ _ _ _ _ _ _ _ xs PreH5 Hlive Hd Hlen PreH18)).
    cancel (copy_call_frame h &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) xs).
    cancel (copy_lookup_cells (copy_table a d0) sizeof("slot") 17 xs); cancel.
  - sep_apply_l_atomic (proj1 (copy_resources_sentinel__lookup &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot") d0 (copy_table a d0) (copy_counter a d0) xs ltac:(lia))).
    cancel (copy_heap h); cancel.
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_9 : ucos_CNode_Copy_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Copy_entail_wit_9_split_goal_spatial.
  - Goal_apply proof_of_ucos_CNode_Copy_entail_wit_9_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_10_split_goal_spatial : ucos_CNode_Copy_entail_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; subst; repeat split; assumption).
  destruct PreH5 as [_ [ND [_ [_ [_ [_ RO]]]]]].
  destruct (RO LIVE PreH12) as [_ [_ RR]].
  subst lookup_object idx.
  destruct (RR 0 PreH14) as [RC _].
  specialize (RC eq_refl).
  change (copy_heap h |-- copy_hole h (&("OSCSpaceObjectPointer") + d0 * 4) ** store_uint (&("OSCSpaceObjectPointer") + d0 * 4) (copy_counter a d0)).
  replace (d0 * 4) with (4*d0) by ring.
  apply (copy_read_focus__access h _ false _ ND RC).
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_10 : ucos_CNode_Copy_entail_wit_10.
Proof. aggressive_pre_process. Goal_apply proof_of_ucos_CNode_Copy_entail_wit_10_split_goal_spatial. Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_11_1 : ucos_CNode_Copy_entail_wit_11_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; repeat split; congruence).
 assert (AV := copy_available__allocation h a _ _ _ _ d0 s0 f0 0 PreH5 LIVE PreH12).
 rewrite <- PreH13 in AV. specialize (AV PreH15).
 destruct AV as [AV _]. specialize (AV eq_refl PreH1).
 destruct AV as [W [B _]].
 Exists (copy_put h (( &( "OSCSpaceObjectPointer" ) ) + 4*d0) (copy_counter a d0+1)).
 split_pure_spatial.
 - replace (d0 * sizeof(UINT)) with (4*d0) by (rewrite sizeof_uint; ring).
   apply copy_heap_put__allocation; [exact (proj1 (proj2 PreH5))|exact W].
 - split_pures; try (dump_pre_spatial; assumption).
   dump_pre_spatial. unfold copy_allocation_state. left. repeat split; auto; lia.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_11_2_split_goal_1 : ucos_CNode_Copy_entail_wit_11_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; repeat split; congruence).
 pose proof (copy_available__allocation h a _ _ _ _ d0 s0 f0 idx PreH5 LIVE PreH12) as AV.
 rewrite <- PreH13 in AV. specialize (AV PreH14). destruct AV as [_ AV]. specialize (AV PreH1).
 destruct AV as [B _]. unfold copy_allocation_state. right.
 subst pCSpace2 lookup_object. repeat split; auto; lia.
Qed.

Lemma proof_of_ucos_CNode_Copy_entail_wit_11_2 : ucos_CNode_Copy_entail_wit_11_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_ucos_CNode_Copy_entail_wit_11_2_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_12 : ucos_CNode_Copy_entail_wit_12.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 assert (LIVE : copy_live a d0 s0 f0) by (unfold copy_live; repeat split; congruence).
 pose proof (copy_allocation_tag__allocation h hc_2 a _ _ _ _ d0 s0 f0 lookup_object idx PreH4 LIVE PreH11 PreH12 PreH13) as [ND W].
 Exists hc_2. split_pure_spatial.
 - rewrite PreH5. change (copy_heap hc_2 |-- copy_hole hc_2 (copy_tag_address (copy_table a d0) sizeof( "slot" ) idx) ** undef_store_uint (copy_tag_address (copy_table a d0) sizeof( "slot" ) idx)).
   apply copy_heap_writable__allocation; assumption.
 - split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_13 : ucos_CNode_Copy_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia).
  assert (LIVE : copy_live a d0 s0 f0).
  { unfold copy_live; repeat split; congruence. }
  pose proof (copy_object_resources__object_steps h hc_2 a
    &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot")
    d0 s0 f0 idx PreH4 LIVE PreH11 ltac:(rewrite <- PreH12; exact PreH13))
    as [ND [WT [RW [WW [RP [WP [N1 [N2 N3]]]]]]]].
  assert (ET : &(cap1 # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") idx).
  { subst cap1 pCSpace1. unfold copy_tag_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_right").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_right").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_t").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  rewrite <- ET in WT, N1, N2.
  rewrite <- EW1 in WW, N3. rewrite <- EW2 in RW, N1.
  rewrite <- EP1 in WP. rewrite <- EP2 in RP, N2, N3.
  set (xt := &(cap1 # "cap" ->ₛ "cap_type")) in *.
  set (xw := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (yw := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (xp := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (yp := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (w := copy_word0 (copy_slots a (copy_table a s0) f0)) in *.
  set (ptr := copy_pointer (copy_slots a (copy_table a s0) f0)) in *.
  set (ht := copy_put hc_2 xt 2).
  assert (NDT : NoDup (map copy_cell_addr ht))
    by (unfold ht; rewrite copy_put_preserves__object_steps; exact ND).
  assert (RWT : copy_read ht yw false w)
    by (apply copy_read_put_other__object_steps; assumption).
  assert (WWT : copy_writable ht xw false)
    by (apply copy_writable_put__object_steps; assumption).
  destruct WT as [old WT].
  sep_apply_l_atomic (copy_heap_put__object_steps hc_2 xt false old 2 ND WT).
  fold ht.
  destruct (Z.eq_dec xw yw) as [EQ|NE].
  - Right. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (proj1 (copy_heap_focus__object_steps ht
        {|copy_cell_addr:=yw;copy_cell_ptr:=false;copy_cell_value:=Some w|} NDT RWT)).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht.
      cancel (copy_hole ht yw). cancel (store_uint yw w).
    + split_pures; dump_pre_spatial; auto.
  - Left. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (copy_heap_prepare__object_steps ht xw yw false w NDT RWT WWT NE).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht.
      cancel (copy_two_holes ht xw yw). cancel (store_uint yw w). cancel (undef_store_uint xw).
    + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_14_1 : ucos_CNode_Copy_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (LIVE : copy_live a d0 s0 f0).
  { unfold copy_live; repeat split; congruence. }
  pose proof (copy_object_resources__object_steps h hc_2 a
    &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot")
    d0 s0 f0 idx PreH4 LIVE PreH11 ltac:(rewrite <- PreH12; exact PreH13))
    as [ND [WT [RW [WW [RP [WP [N1 [N2 N3]]]]]]]].
  assert (ET : &(cap1 # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") idx).
  { subst cap1 pCSpace1. unfold copy_tag_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_right").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_right").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_t").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  rewrite <- ET in WT, N1, N2.
  rewrite <- EW1 in WW, N3. rewrite <- EW2 in RW, N1.
  rewrite <- EP1 in WP. rewrite <- EP2 in RP, N2, N3.
  set (xt := &(cap1 # "cap" ->ₛ "cap_type")) in *.
  set (xw := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (yw := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (xp := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (yp := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (w := copy_word0 (copy_slots a (copy_table a s0) f0)) in *.
  set (ptr := copy_pointer (copy_slots a (copy_table a s0) f0)) in *.
  set (ht := copy_put hc_2 xt 2).
  assert (NDT : NoDup (map copy_cell_addr ht))
    by (unfold ht; rewrite copy_put_preserves__object_steps; exact ND).
  assert (RWT : copy_read ht yw false w)
    by (apply copy_read_put_other__object_steps; assumption).
  assert (WWT : copy_writable ht xw false)
    by (apply copy_writable_put__object_steps; assumption).
  set (hw := copy_put ht xw w).
  assert (NDW : NoDup (map copy_cell_addr hw))
    by (unfold hw; rewrite copy_put_preserves__object_steps; exact NDT).
  assert (RPW : copy_read hw yp true ptr).
  { apply copy_read_put_other__object_steps; [exact N3|].
    apply copy_read_put_other__object_steps; assumption. }
  assert (WPW : copy_writable hw xp true).
  { apply copy_writable_put__object_steps.
    apply copy_writable_put__object_steps; exact WP. }
  destruct WWT as [old WWT].
  fold ht.
  sep_apply_l_atomic (copy_heap_two_put__object_steps ht xw yw false old w w NDT WWT RWT PreH14).
  fold ht hw.
  destruct (Z.eq_dec xp yp) as [EQ|NE].
  - Right. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (proj1 (copy_heap_focus__object_steps hw
        {|copy_cell_addr:=yp;copy_cell_ptr:=true;copy_cell_value:=Some ptr|} NDW RPW)).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht hw.
      cancel (copy_hole hw yp). cancel (store_ptr yp ptr).
    + split_pures; dump_pre_spatial; auto.
  - Left. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (copy_heap_prepare__object_steps hw xp yp true ptr NDW RPW WPW NE).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht hw.
      cancel (copy_two_holes hw xp yp). cancel (store_ptr yp ptr). cancel (undef_store_ptr xp).
    + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_entail_wit_14_2 : ucos_CNode_Copy_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(lia).
  assert (LIVE : copy_live a d0 s0 f0).
  { unfold copy_live; repeat split; congruence. }
  pose proof (copy_object_resources__object_steps h hc_2 a
    &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer") sizeof(PTR) sizeof("slot")
    d0 s0 f0 idx PreH4 LIVE PreH11 ltac:(rewrite <- PreH12; exact PreH13))
    as [ND [WT [RW [WW [RP [WP [N1 [N2 N3]]]]]]]].
  assert (ET : &(cap1 # "cap" ->ₛ "cap_type") = copy_tag_address (copy_table a d0) sizeof("slot") idx).
  { subst cap1 pCSpace1. unfold copy_tag_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_right").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EW2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_right").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP1 : &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a d0) sizeof("slot") idx "object_t").
  { subst cap1 pCSpace1. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  assert (EP2 : &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") =
    copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t").
  { subst cap2 pCSpace2. unfold copy_object_address, copy_slot_lvalue. csimpl. reflexivity. }
  rewrite <- ET in WT, N1, N2.
  rewrite <- EW1 in WW, N3. rewrite <- EW2 in RW, N1.
  rewrite <- EP1 in WP. rewrite <- EP2 in RP, N2, N3.
  set (xt := &(cap1 # "cap" ->ₛ "cap_type")) in *.
  set (xw := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (yw := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) in *.
  set (xp := &(cap1 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (yp := &(cap2 # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) in *.
  set (w := copy_word0 (copy_slots a (copy_table a s0) f0)) in *.
  set (ptr := copy_pointer (copy_slots a (copy_table a s0) f0)) in *.
  set (ht := copy_put hc_2 xt 2).
  assert (NDT : NoDup (map copy_cell_addr ht))
    by (unfold ht; rewrite copy_put_preserves__object_steps; exact ND).
  assert (RWT : copy_read ht yw false w)
    by (apply copy_read_put_other__object_steps; assumption).
  assert (WWT : copy_writable ht xw false)
    by (apply copy_writable_put__object_steps; assumption).
  set (hw := copy_put ht xw w).
  assert (NDW : NoDup (map copy_cell_addr hw))
    by (unfold hw; rewrite copy_put_preserves__object_steps; exact NDT).
  assert (RPW : copy_read hw yp true ptr).
  { apply copy_read_put_other__object_steps; [exact N3|].
    apply copy_read_put_other__object_steps; assumption. }
  assert (WPW : copy_writable hw xp true).
  { apply copy_writable_put__object_steps.
    apply copy_writable_put__object_steps; exact WP. }
  assert (RX : copy_read ht xw false w) by (rewrite PreH14; exact RWT).
  fold ht. rewrite <- PreH14.
  sep_apply_l_atomic (copy_heap_put__object_steps ht xw false (Some w) w NDT RX).
  fold ht hw.
  destruct (Z.eq_dec xp yp) as [EQ|NE].
  - Right. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (proj1 (copy_heap_focus__object_steps hw
        {|copy_cell_addr:=yp;copy_cell_ptr:=true;copy_cell_value:=Some ptr|} NDW RPW)).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht hw.
      cancel (copy_hole hw yp). cancel (store_ptr yp ptr).
    + split_pures; dump_pre_spatial; auto.
  - Left. Exists hc_2. split_pure_spatial.
    + sep_apply_l_atomic (copy_heap_prepare__object_steps hw xp yp true ptr NDW RPW WPW NE).
      unfold copy_cell_heap; cbn [copy_cell_addr copy_cell_ptr copy_cell_value]. fold ht hw.
      cancel (copy_two_holes hw xp yp). cancel (store_ptr yp ptr). cancel (undef_store_ptr xp).
    + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_1 : ucos_CNode_Copy_return_wit_1.
Proof.
 LLM_pre_process ltac:(lia). subst pCSpace1 pCSpace2.
 change (cap1 = copy_cap_address (copy_table a d0) sizeof("slot") f0) in PreH9.
 change (cap2 = copy_cap_address (copy_table a s0) sizeof("slot") f0) in PreH10.
 subst cap1 cap2.
 rewrite !copy_category_address_bridge__category_result in *.
 rewrite !copy_tag_address_bridge__category_result in *.
 set (stride := sizeof( "slot" )).
 set (x := copy_category_address (copy_table a d0) stride f0 "category_right").
 set (y := copy_category_address (copy_table a s0) stride f0 "category_right").
 set (t := copy_tag_address (copy_table a d0) stride f0).
 set (c := copy_category_address (copy_table a d0) stride f0 "category_content").
 set (v := copy_word1 (copy_slots a (copy_table a s0) f0)).
 set (w := copy_word0 (copy_slots a (copy_table a s0) f0)).
 set (hh := copy_put (copy_put h t 1) c w).
 change (x = y) in PreH12.
 change (store_uint x v ** copy_hole hh y |-- EX hout, “copy_post h hout a &("OSCSpaceObjectPointer") stride d0 s0 f0 0” && copy_heap hout).
 assert (Live: copy_live a d0 s0 f0) by (unfold copy_live; auto).
 pose proof PreH4 as HP. unfold copy_pre in HP.
 destruct HP as [Safe [ND [Layout [Tables [Tags [Cat Obj]]]]]].
 destruct (Cat Live PreH11) as [R0 [R1 [WT [WC WX]]]].
 assert (NDh: NoDup (map copy_cell_addr hh)) by (unfold hh; rewrite !copy_put_addresses__category_result; exact ND).
 assert (WXh: copy_writable hh x false) by (unfold hh; repeat apply copy_put_writable__category_result; exact WX).
 rewrite <- PreH12.
 sep_apply_l_atomic (copy_heap_put__category_result hh x v NDh WXh).
 Exists (copy_put hh x v).
 split_pure_spatial; [cancel|].
 split_pures. dump_pre_spatial.
 exact (copy_category_post__category_result h a &("OSCSpaceObjectPointer") stride d0 s0 f0 Live PreH11).
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_2 : ucos_CNode_Copy_return_wit_2.
Proof.
 LLM_pre_process ltac:(lia). subst pCSpace1 pCSpace2.
 change (cap1 = copy_cap_address (copy_table a d0) sizeof("slot") f0) in PreH9.
 change (cap2 = copy_cap_address (copy_table a s0) sizeof("slot") f0) in PreH10.
 subst cap1 cap2.
 rewrite !copy_category_address_bridge__category_result in *.
 rewrite !copy_tag_address_bridge__category_result in *.
 set (stride := sizeof( "slot" )).
 set (x := copy_category_address (copy_table a d0) stride f0 "category_right").
 set (y := copy_category_address (copy_table a s0) stride f0 "category_right").
 set (t := copy_tag_address (copy_table a d0) stride f0).
 set (c := copy_category_address (copy_table a d0) stride f0 "category_content").
 set (v := copy_word1 (copy_slots a (copy_table a s0) f0)).
 set (w := copy_word0 (copy_slots a (copy_table a s0) f0)).
 set (hh := copy_put (copy_put h t 1) c w).
 change (x <> y) in PreH12.
 change (copy_two_holes hh x y ** (store_uint y v ** store_uint x v) |-- EX hout, “copy_post h hout a &("OSCSpaceObjectPointer") stride d0 s0 f0 0” && copy_heap hout).
 assert (Live: copy_live a d0 s0 f0) by (unfold copy_live; auto).
 pose proof PreH4 as HP. unfold copy_pre in HP.
 destruct HP as [Safe [ND [Layout [Tables [Tags [Cat Obj]]]]]].
 destruct (Cat Live PreH11) as [R0 [R1 [WT [WC WX]]]].
 assert (NDh: NoDup (map copy_cell_addr hh)) by (unfold hh; rewrite !copy_put_addresses__category_result; exact ND).
 assert (WXh: copy_writable hh x false) by (unfold hh; repeat apply copy_put_writable__category_result; exact WX).
 assert (F: 0 <= f0 < 255).
 { destruct Safe as [[HD [HS HF]] Safety]. lia. }
 destruct (Layout Live) as [Aliases [Inject Rest]].
 assert (TY: t <> y).
 { intro E. assert (EC: copy_component_address (copy_table a d0) stride f0 0 = copy_component_address (copy_table a s0) stride f0 2).
   { unfold copy_component_address; simpl; exact E. }
   pose proof (Inject (copy_table a d0) (copy_table a s0) f0 f0 0 2 (or_introl eq_refl) (or_intror eq_refl) F F ltac:(lia) ltac:(lia) EC) as Contra. lia. }
 assert (CY: c <> y).
 { intro E. assert (EC: copy_component_address (copy_table a d0) stride f0 1 = copy_component_address (copy_table a s0) stride f0 2).
   { unfold copy_component_address; simpl; exact E. }
   pose proof (Inject (copy_table a d0) (copy_table a s0) f0 f0 1 2 (or_introl eq_refl) (or_intror eq_refl) F F ltac:(lia) ltac:(lia) EC) as Contra. lia. }
 assert (RYh: copy_read hh y false v).
 { unfold hh. apply copy_put_read__category_result; auto. apply copy_put_read__category_result; auto. }
 sep_apply_l_atomic (copy_heap_two_focus__category_result hh x y v v NDh PreH12 WXh RYh).
 Exists (copy_put hh x v).
 split_pure_spatial; [cancel|].
 split_pures. dump_pre_spatial.
 exact (copy_category_post__category_result h a &("OSCSpaceObjectPointer") stride d0 s0 f0 Live PreH11).
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_3 : ucos_CNode_Copy_return_wit_3.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst.
 assert (ND : NoDup (map copy_cell_addr h)) by (destruct PreH6 as (_ & HH & _); exact HH).
 assert (RD : copy_read h (copy_tag_address (copy_table a s0) (sizeof( "slot" )) f0) false (copy_tag (copy_slots a (copy_table a s0) f0))).
 { pose proof PreH6 as HP. destruct HP as (_ & _ & _ & _ & HT & _). apply HT. unfold copy_live; repeat split; assumption. }
 Exists h. split_pure_spatial.
 - try replace (4*d0) with (d0*4) in RD by ring.
   try replace (sizeof(PTR)*s0) with (s0*sizeof(PTR)) in RD by ring.
   unfold copy_read in RD.
   rewrite (copy_heap_focus__unchanged_result h _ ND RD).
   unfold copy_cell_heap. simpl.
   unfold copy_tag_address, copy_slot_lvalue. simpl.
   csimpl. cancel.
 - dump_pre_spatial. apply copy_unchanged_post__unchanged_result; [|lia].
   unfold copy_result. right. split; [assumption|]. split; [assumption|]. split; [assumption|]. right. split; [assumption|]. split; [assumption|]. right. left. repeat split; try assumption; unfold copy_state_same; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_4 : ucos_CNode_Copy_return_wit_4.
Proof.
 LLM_pre_process ltac:(lia).
 change (cap1 = copy_cap_address pCSpace1 sizeof("slot") idx) in PreH9.
 change (cap2 = copy_cap_address pCSpace2 sizeof("slot") f0) in PreH10.
 subst cap1 cap2 pCSpace1 pCSpace2.
 repeat rewrite copy_tag_concrete__object_result in *.
 repeat rewrite copy_object_concrete__object_result in *.
 assert (Live : copy_live a d0 s0 f0) by (unfold copy_live; auto).
 pose proof (copy_object_ready__object_result h hc a &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer")
   sizeof(PTR) sizeof("slot") d0 s0 f0 lookup_object idx PreH4 Live PreH11 PreH12 PreH13) as Ready.
 set (h2 := copy_put (copy_put hc (copy_tag_address (copy_table a d0) sizeof("slot") idx) 2)
   (copy_object_address (copy_table a d0) sizeof("slot") idx "object_right")
   (copy_word0 (copy_slots a (copy_table a s0) f0))) in *.
 set (x := copy_object_address (copy_table a d0) sizeof("slot") idx "object_t") in *.
 set (y := copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t") in *.
 set (v := copy_pointer (copy_slots a (copy_table a s0) f0)) in *.
 destruct Ready as [ND [Writable Read]].
 Exists (copy_write_all hc (copy_object_delta a sizeof("slot") d0 s0 f0 idx)).
 split_pure_spatial.
 - change (copy_two_holes h2 x y ** (store_ptr y v ** store_ptr x v)
     |-- copy_heap (copy_put h2 x v)).
   sep_apply_l_atomic (copy_heap_two_focus__object_result h2 x y v v ND PreH14 Writable Read).
   cancel.
 - dump_pre_spatial. eapply copy_object_post__object_result; eauto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_5 : ucos_CNode_Copy_return_wit_5.
Proof.
 LLM_pre_process ltac:(lia).
 change (cap1 = copy_cap_address pCSpace1 sizeof("slot") idx) in PreH9.
 change (cap2 = copy_cap_address pCSpace2 sizeof("slot") f0) in PreH10.
 subst cap1 cap2 pCSpace1 pCSpace2.
 repeat rewrite copy_tag_concrete__object_result in *.
 repeat rewrite copy_object_concrete__object_result in *.
 assert (Live : copy_live a d0 s0 f0) by (unfold copy_live; auto).
 pose proof (copy_object_ready__object_result h hc a &("OSCSpacePrioTbl") &("OSCSpaceObjectPointer")
   sizeof(PTR) sizeof("slot") d0 s0 f0 lookup_object idx PreH4 Live PreH11 PreH12 PreH13) as Ready.
 set (h2 := copy_put (copy_put hc (copy_tag_address (copy_table a d0) sizeof("slot") idx) 2)
   (copy_object_address (copy_table a d0) sizeof("slot") idx "object_right")
   (copy_word0 (copy_slots a (copy_table a s0) f0))) in *.
 set (x := copy_object_address (copy_table a d0) sizeof("slot") idx "object_t") in *.
 set (y := copy_object_address (copy_table a s0) sizeof("slot") f0 "object_t") in *.
 set (v := copy_pointer (copy_slots a (copy_table a s0) f0)) in *.
 destruct Ready as [ND [Writable Read]].
 Exists (copy_write_all hc (copy_object_delta a sizeof("slot") d0 s0 f0 idx)).
 split_pure_spatial.
 - change (store_ptr x v ** copy_hole h2 y |-- copy_heap (copy_put h2 x v)).
   rewrite <- PreH14.
   sep_apply_l_atomic (copy_heap_put__object_result h2 x true v ND Writable).
   cancel.
 - dump_pre_spatial. eapply copy_object_post__object_result; eauto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_6 : ucos_CNode_Copy_return_wit_6.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst.
 assert (ND : NoDup (map copy_cell_addr h)) by (destruct PreH5 as (_ & HH & _); exact HH).
 assert (RD : copy_read h (( &( "OSCSpaceObjectPointer" ) ) + 4*d0) false (copy_counter a d0)).
 { pose proof PreH5 as HP. destruct HP as (_ & _ & _ & _ & _ & _ & HO). destruct (HO ltac:(unfold copy_live; repeat split; assumption) PreH12) as (_ & _ & HR). exact (proj1 (HR 0 PreH15) eq_refl). }
 Exists h. split_pure_spatial.
 - try replace (4*d0) with (d0*4) in RD by ring.
   try replace (sizeof(PTR)*s0) with (s0*sizeof(PTR)) in RD by ring.
   unfold copy_read in RD.
   rewrite (copy_heap_focus__unchanged_result h _ ND RD).
   unfold copy_cell_heap. simpl.
   unfold copy_tag_address, copy_slot_lvalue. simpl.
   csimpl. cancel.
 - dump_pre_spatial. apply copy_unchanged_post__unchanged_result; [|lia].
   unfold copy_result. right. split; [assumption|]. split; [assumption|]. split; [assumption|]. right. split; [assumption|]. split; [assumption|]. right. right. split; [assumption|]. exists 0. split; [assumption|]. left. repeat split; try lia; unfold copy_state_same; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_7 : ucos_CNode_Copy_return_wit_7.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst.
 assert (ND : NoDup (map copy_cell_addr h)) by (destruct PreH5 as (_ & HH & _); exact HH).
 assert (RD : copy_read h (( &( "OSCSpacePrioTbl" ) ) + sizeof(PTR)*s0) true (copy_table a s0)).
 { pose proof PreH5 as HP. destruct HP as (_ & _ & _ & HT & _). exact (proj2 (HT ltac:(assumption) ltac:(assumption) ltac:(assumption))). }
 Exists h. split_pure_spatial.
 - try replace (4*d0) with (d0*4) in RD by ring.
   try replace (sizeof(PTR)*s0) with (s0*sizeof(PTR)) in RD by ring.
   unfold copy_read in RD.
   rewrite (copy_heap_focus__unchanged_result h _ ND RD).
   unfold copy_cell_heap. simpl.
   unfold copy_tag_address, copy_slot_lvalue. simpl.
   csimpl. cancel.
 - dump_pre_spatial. apply copy_unchanged_post__unchanged_result; [|lia].
   unfold copy_result. right. split; [assumption|]. split; [assumption|]. split; [assumption|]. left. split; [auto|]. split; [reflexivity|]. unfold copy_state_same; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_8 : ucos_CNode_Copy_return_wit_8.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst.
 assert (ND : NoDup (map copy_cell_addr h)) by (destruct PreH6 as (_ & HH & _); exact HH).
 assert (RD : copy_read h (( &( "OSCSpacePrioTbl" ) ) + sizeof(PTR)*s0) true (copy_table a s0)).
 { pose proof PreH6 as HP. destruct HP as (_ & _ & _ & HT & _). exact (proj2 (HT ltac:(assumption) ltac:(assumption) ltac:(assumption))). }
 Exists h. split_pure_spatial.
 - try replace (4*d0) with (d0*4) in RD by ring.
   try replace (sizeof(PTR)*s0) with (s0*sizeof(PTR)) in RD by ring.
   unfold copy_read in RD.
   rewrite (copy_heap_focus__unchanged_result h _ ND RD).
   unfold copy_cell_heap. simpl.
   unfold copy_tag_address, copy_slot_lvalue. simpl.
   csimpl. cancel.
 - dump_pre_spatial. apply copy_unchanged_post__unchanged_result; [|lia].
   unfold copy_result. right. split; [assumption|]. split; [assumption|]. split; [assumption|]. left. split; [auto|]. split; [reflexivity|]. unfold copy_state_same; auto.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_9_split_goal_1 : ucos_CNode_Copy_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_post.
  exists a, (@nil (Z * Z)).
  split.
  - unfold copy_result. left.
    split; [lia |].
    split; [reflexivity |].
    unfold copy_state_same. repeat split; intros; reflexivity.
  - split.
    + unfold copy_delta. left. split; [lia | reflexivity].
    + reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Copy_return_wit_9 : ucos_CNode_Copy_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Copy_return_wit_9_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_10_split_goal_1 : ucos_CNode_Copy_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_post.
  exists a, (@nil (Z * Z)).
  split.
  - unfold copy_result. left.
    split; [lia |].
    split; [reflexivity |].
    unfold copy_state_same. repeat split; intros; reflexivity.
  - split.
    + unfold copy_delta. left. split; [lia | reflexivity].
    + reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Copy_return_wit_10 : ucos_CNode_Copy_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Copy_return_wit_10_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Copy_return_wit_11_split_goal_1 : ucos_CNode_Copy_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_post.
  exists a, (@nil (Z * Z)).
  split.
  - unfold copy_result. left.
    split; [lia |].
    split; [reflexivity |].
    unfold copy_state_same. repeat split; intros; reflexivity.
  - split.
    + unfold copy_delta. left. split; [lia | reflexivity].
    + reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Copy_return_wit_11 : ucos_CNode_Copy_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Copy_return_wit_11_split_goal_1.
Qed. 

