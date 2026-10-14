
Require Import abs_op.
Require Import inv_prop.

Require Import Lia.
Require Import ucos_include.
Require Import oscore_common.
Require Import symbolic_lemmas.

(* Require Import q_common_ext. *)
Require Import OSEventRemovePure.

Require Import seplog_trm_tacs.

Require Import ifun_spec. 

Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Lemma evsllseg_tnptr_hdptr:
  forall vl hd tn edl s P, 
    s |= evsllseg hd tn vl edl ** P ->
    isptr tn ->
    isptr hd.
Proof.
  destruct vl.
  -
    intros.
    unfold evsllseg in H. sep split in H. simpljoin1. auto.
  -
    introv Hsat Hptr.
    unfold evsllseg in Hsat.
    fold evsllseg in Hsat.
    destruct edl.
    destruct Hsat. simpljoin1. tryfalse.
    destruct e; destruct p.
    sep pure.
    destruct Hsat. simpljoin1.
    unfold AEventNode in H4.
    unfold AOSEvent in H4.
    sep normal in H4. sep pure.
    unfold node in H4. sep pure.
    simpljoin1.
    apply ptr_isptr.
Qed.   

Lemma evsllseg_hd_not_null:
  forall vhd tn_addr ectrl enl s P, 
    s |= evsllseg vhd (Vptr tn_addr) ectrl enl ** P ->
    vhd <> Vnull.
Proof.
  introv Hsat.
  destruct ectrl.
  -
    unfold evsllseg in Hsat.
    sep pure.
    simpljoin1.
    pure_auto.
  -
    unfold evsllseg in Hsat; fold evsllseg in Hsat.
    destruct enl.
    destruct Hsat; simpljoin1.
    tryfalse.
    destruct e; destruct p.
    sep pure.
    unfold AEventNode in Hsat.
    unfold AOSEvent in Hsat.
    sep pure.
    unfold node in Hsat.
    sep pure.
    simpljoin1.
    pure_auto. 
Qed.

Lemma AEventNode_hd_vptr:
  forall x x0 x1 x2 x3 s P, 
    s |= AEventNode x x0 x1 x2 x3 ** P -> exists a, x = Vptr (a, Int.zero). 
Proof.
  introv Hsat.
  unfold AEventNode in Hsat.
  unfold AOSEvent in Hsat.
  sep pure.
  unfold node in Hsat.
  sep pure.
  simpljoin1.
  eexists; eauto.
Qed.

Open Scope list_scope.

Lemma evsllseg_has_node' :
  forall s x l1 l2 tn,
    s |= evsllseg (Vptr x) tn l1 l2 ->
    Vptr x <> tn -> 
    exists h1 t1 h2 t2, l1 = h1 :: t1 /\ l2 = h2 :: t2.
Proof.
  intros.
  destruct l1.
  simpl in H; simpljoin1; tryfalse.
  destruct l2; simpl in H; simpljoin1; tryfalse.
  do 4 eexists.
  eauto.
Qed.

Lemma evsllseg_append1: 
  forall (v'9:list EventCtr) (v'11:list EventData) v'6 v'13 v'12 x4 (v1:val) x6 v'8 x8 v'10 v0 v1 v'9 v'11 s d i0 v pegrp lptbl,
    RL_Tbl_Grp_P v0 v'12 -> 
    id_addrval' (Vptr (v'13, Int.zero)) os_code_defs.OSEventTbl os_ucos_h.OS_EVENT = Some v'10 ->
    RL_Tbl_Grp_P v pegrp ->
    id_addrval' (Vptr (v'13, Int.zero)) OSPostEventTbl os_ucos_h.OS_EVENT = Some lptbl ->
    struct_type_vallist_match os_ucos_h.OS_EVENT (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) ->
    s |= evsllseg v'6 (Vptr (v'13, Int.zero)) v'9 v'11 **
      Astruct (v'13, Int.zero) os_ucos_h.OS_EVENT(i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) **
      AOSEventTbl v'10 v0 **
      AOSPostEventTbl lptbl v **
      AEventData (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) d ->
    s |= evsllseg v'6 v'8 (v'9 ++ (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8, v0, v) :: nil) (v'11 ++ d :: nil).
Proof.
  intros. 
  apply evsllseg_merge' with (y:=(Vptr (v'13, Int.zero))).
  sep cancel evsllseg.
  unfold evsllseg.
  exists v'8.
  sep split; eauto.
  unfold AEventNode.
  sep cancel AEventData.
  unfold AOSEvent.
  unfold node.
  sep pauto.
  eauto.
  go.
  eauto.
  go. 
Qed.

Lemma evsllseg_append1_frm: 
  forall (v'9:list EventCtr) (v'11:list EventData) v'6 v'13 v'12 x4 (v1:val) x6 v'8 x8 v'10 v0 v1 v'9 v'11 s d i0 v pegrp lptbl P,
    RL_Tbl_Grp_P v0 v'12 -> 
    id_addrval' (Vptr (v'13, Int.zero)) os_code_defs.OSEventTbl os_ucos_h.OS_EVENT = Some v'10 ->
    RL_Tbl_Grp_P v pegrp ->
    id_addrval' (Vptr (v'13, Int.zero)) OSPostEventTbl os_ucos_h.OS_EVENT = Some lptbl ->
    struct_type_vallist_match os_ucos_h.OS_EVENT (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) ->
    s |= evsllseg v'6 (Vptr (v'13, Int.zero)) v'9 v'11 **
      Astruct (v'13, Int.zero) os_ucos_h.OS_EVENT(i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) **
      AOSEventTbl v'10 v0 **
      AOSPostEventTbl lptbl v **
      AEventData (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8) d **
      P ->
    s |= evsllseg v'6 v'8 (v'9 ++ (i0 :: v'12 :: x4 :: v1 :: x6 :: v'8 :: pegrp :: x8, v0, v) :: nil) (v'11 ++ d :: nil) ** P.
Proof.
  intros.
  sep cancel P.
  eapply evsllseg_append1; eauto. 
Qed. 

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto);
  destruct h as [Ht | Hf].

Lemma nval_inj_neqz_neqptr: 
  forall v'2 tn_addr, 
    val_inj (notint (val_inj (val_eq v'2 (Vptr tn_addr)))) <> Vint32 Int.zero ->
    v'2 <> Vptr tn_addr.
Proof.
  intros. 
  casetac v'2 (Vptr tn_addr) Ht Hf.
  subst. simpl in H. destruct tn_addr.
  false. apply H. clear. pure_auto.
  asserts_rewrite (Int.eq i i = true) in HeqH0.
  { clear. int auto. }
  tryfalse.
  auto.
Qed.   

Lemma ptr_in_ectrls_singleton_false:
  forall hd p p' v0 v1 v2 v3 v4 x' et pet, 
    isptr hd ->
    isptr p -> 
    hd <> p ->
    p' <> p ->
    ptr_in_ectrls hd ((v0::v1::v2::v3::v4::p'::x', et, pet)::nil) p = false.
Proof.
  intros.
  unfolds.
  destruct (val_beq hd p) eqn: E.
  apply val_beq_true_eq in E. subst. tryfalse.
  simpl. auto.
Qed. 

Lemma evsllseg_eq_hd_tn_node_nil:
  forall a ectrl enl osev et pet s P, 
    s |= evsllseg (Vptr a) (Vptr a) ectrl enl ** AOSEvent (Vptr a) osev et pet ** P -> 
    ectrl = nil /\ enl = nil. 
Proof.
  introv Hsat.
  destruct ectrl.
  unfold evsllseg in Hsat.
  sep pure.
  simpljoin; auto.
  unfold evsllseg in Hsat; fold evsllseg in Hsat.
  destruct enl.
  destruct Hsat; simpljoin1.
  tryfalse.
  destruct e; destruct p.
  sep pure.
  unfold AEventNode in Hsat.
  unfold AOSEvent in Hsat.
  unfold node in Hsat. 
  sep pure.
  simpljoin1.
  sep_lifts_trms_in Hsat (Astruct (x4, Int.zero)).
  rewrite H0 in H7. inverts H7.
  apply sep_ptr_neq_OS_EVENT in Hsat.
  false. 
Qed. 

Require Import protect.
Require Import os_ucos_h. 

Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope. 

Lemma OS_EventRemoveQDel_proof: 
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OS_EventRemoveDel vl logicl OS_EventRemoveDelPre ct->
    Some r =
    BuildRetI os_internal OS_EventRemoveDel vl logicl OS_EventRemoveDelPost ct-> 
    exists t d1 d2 s,
      os_internal OS_EventRemoveDel = Some (t, d1, d2, s) /\ 
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec. 

  rename v'9 into aop.
  inverts H.
  rename v'11 into ier.
  rename v'3 into ectrl.
  rename v'2 into enl. (* list of enodes *)
  rename v'4 into vhd.
  rename v'5 into tn_addr. 
  rename v'6 into osevent. 
  hoare_assert_pure (ectrl = nil -> enl = nil /\ Vptr tn_addr = vhd).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat (evsllseg vhd).
    subst ectrl.
    unfold evsllseg at 1 in Hsat.
    sep split in Hsat; simpljoin1; splits; auto. 
  }
  hoare_split_pure_all.
  rename H into Hnil.
  hoare_assert_pure (ectrl <> nil -> Some (Vptr tn_addr) = get_last_ptr ectrl). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (evsllseg vhd). 
    apply evsllseg_get_last_eq_p in Hsat; auto. 
  }
  hoare_split_pure_all.
  rename H into Hnnil.

  hoare_assert_pure (length ectrl = length enl).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (evsllseg vhd). 
    apply evsllseg_list_len_eq in Hsat.
    auto. 
  }
  hoare_split_pure_all.
  rename H into Heqlen. 

  (*L1: p = OSEventList*) 
  hoare forward.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg vhd).
  eapply evsllseg_tnptr_hdptr in Hsat; pauto. 

  (*L2: p1 = OSEventLsit*)
  hoare forward.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg vhd).
  eapply evsllseg_tnptr_hdptr in Hsat; pauto. 

  (*L3: x = 0*)
  hoare forward.
  
  (*L4: if (p == pevent)*)
  hoare_lifts_trms_pre (Aop, x, p1, p, evsllseg vhd, pevent).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  rename H into Hfrm.
  hoare forward.
  get_hsat Hsat; sep_lifts_trms_in Hsat (evsllseg vhd). apply evsllseg_tnptr_hdptr in Hsat; pauto.
  get_hsat Hsat; sep_lifts_trms_in Hsat (evsllseg vhd). apply evsllseg_tnptr_hdptr in Hsat; pauto.
  instantiate (1:=Afalse).

(*L5: OSEventList = OSEventList->OSEventListPtr*)
  (*get the if condition into the context*)
  hoare_split_pure_all.
  simpljoin1.
  (* in the body of the "if", first show vhd = (Vptr tn_addr), according to the condition *)
  assert (Hveq: val_eq vhd (Vptr tn_addr) = Some (Vint32 Int.one)).
  {
    unfold val_eq in *.
    destruct vhd; try solve [simpl in H3; tryfalse].
    destruct tn_addr; simpl in H; tryfalse.
    destruct a, tn_addr.
    destruct (peq b b0); destruct (Int.eq i i0); auto; try solve [simpl in H; tryfalse].
  }
  apply val_eq_true_eq in Hveq.
  substs.
  (* vhd = Vptr tn_addr established *) 

  (*
    ectrl should be nil, and in this case we process the "return"
   *)
  destruct ectrl.
  (*ectrl is nil*)
  (*then enl is nil accordingly*)
  specialize (Hnil (eq_refl _)).
  destruct Hnil as (Hv'2nil & _).
  subst enl.

  unfold AOSEvent.
  unfold node.
  hoare_split_pure_all.
  simpljoin1.
  assert(exists v1 v2 v3 v4 v5 v6 tail, osevent = v1::v2::v3::v4::v5::v6::tail).
  {
    apply struct_type_vallist_match_os_event; auto.
  }
  simpljoin1.
  inverts H0.

  hoare forward.
  auto.
  hoare forward.
  sep pauto. 
  sep cancel Astruct.
  sep cancel AOSEventTbl.
  sep cancel AOSPostEventTbl.
  get_hsat Hsat. 
  unfold evsllseg at 1 in Hsat.
  sep split in Hsat.
  instantiate (1:=nil). instantiate (1:=x4).
  unfold evsllseg. sep auto. 
  
  split.
  intros. splits; eauto.
  introv Hf. false.
  go. go. go.
  eauto.
  auto.
  eauto.
  auto.
  auto.

  (* v'4 is not nil --- impossible *)
  hoare_lifts_trms_pre (evsllseg, AOSEvent). 
  hoare_assert_pure (False).
  {
    get_hsat Hsat.
    unfold evsllseg at 1 in Hsat; fold evsllseg in Hsat.
    destruct enl.
    tryfalse.
    destruct e; destruct p.
    sep pure.
    unfold AEventNode in Hsat.
    unfold AOSEvent in Hsat. sep pure.
    unfold node in Hsat. sep pure.
    simpljoin1.
    asserts_rewrite (x8 = x9) in Hsat.
    { congruence. }
    apply Astruct_osevent_dup_false' in Hsat. 
    auto. 
  }
  hoare_split_pure_all.
  tryfalse. 

  (* event to remove is not the first in the event list *) 
  apply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  rename H into Hinjor. 
  assert (Hneptr: vhd <> (Vptr tn_addr)).
  {
    intro; substs.
    simpl in Hinjor. destruct tn_addr.
    rewrite peq_true in Hinjor; rewrite Int.eq_true in Hinjor.
    simpl in Hinjor; destruct Hinjor; tryfalse.
  }

  hoare_assert_pure (vhd <> Vnull).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    apply evsllseg_hd_not_null in Hsat.
    auto. 
  }
  hoare_split_pure_all.
  rename H into Hhdnn.
  
  (* into the while loop *) 
  (*L7: while (p != (OS_EVENT * )0 && x == 0) *)  
  eapply seq_rule.

  eapply backward_rule1 with
      (p :=
         (EX v ectrla mqla ectrlb mqlb, 
         <|| aop ||> **
             LV x @ Int8u |-> (V$ 0) **
             LV p1 @ os_ucos_h.OS_EVENT ∗ |-> v **
             LV p @ os_ucos_h.OS_EVENT ∗ |-> v **
             evsllseg vhd v ectrla mqla ** 
             evsllseg v (Vptr tn_addr) ectrlb mqlb **
             [| ectrla ++ ectrlb = ectrl /\ mqla ++ mqlb = enl |] ** 
             [| ptr_in_ectrls vhd ectrla (Vptr tn_addr) = false |] ** 
             [| v <> Vptr tn_addr /\ v <> Vnull |] ** 
             LV pevent @ OS_EVENT ∗ |-> Vptr tn_addr ** 
             Hfrm)  \\//
        (EX v vl et pet d ectrl0 mql0, 
         <|| aop ||> **
         LV x @ Int8u |-> (V$ 1) **
         LV p1 @ os_ucos_h.OS_EVENT ∗ |-> Vptr tn_addr **
         LV p @ os_ucos_h.OS_EVENT ∗ |-> v **
         evsllseg vhd v ectrl0 mql0 **
         AEventNode v vl et pet d **
         [| ectrl0 ++ ((vl, et, pet) :: nil) = ectrl /\ mql0 ++ (d::nil) = enl |] ** 
         [| v <> Vptr tn_addr /\ ptr_in_ectrls vhd ectrl0 (Vptr tn_addr) = false |] ** 
         [| V_OSEventListPtr vl = Some (Vptr tn_addr) |] **
         LV pevent @ OS_EVENT ∗ |-> Vptr tn_addr ** 
         Hfrm) 
      ).

  (*before the while loop, prove PRE implies the LOOP INV*)
  introv Hsat.
  left.
  exists vhd.
  exists (nil : list os_inv.EventCtr).
  exists (nil : list EventData).
  exists ectrl.
  exists enl.
  do 4 sep cancel 1%nat 1%nat.
  unfold evsllseg at 1.
  sep cancel evsllseg.
  sep pauto.
  apply ptr_in_ectrls_nil_false; auto. 
  
  (*loop inv of while in pre condition*)
  eapply while_rule.
  
  introv Hsat.
  destruct Hsat as [Hs | Hs].
  {
    sep destruct Hs. 
    sep_lifts_trms_in Hs (evsllseg x).
    lets H00: evsllseg_tnptr_hdptr Hs (ptr_isptr tn_addr); pauto.
    symbolic execution; pauto.
    rewrite Int.eq_true.
    destruct H00.
    subst. simpl. pure_auto.
    simpljoin1; subst. simpl. destruct x4. pure_auto. 
  }
  {
    sep destruct Hs. 
    assert (exists p, x = Vptr p).
    {
      sep_lifts_trms_in Hs AEventNode.
      apply AEventNode_hd_vptr in Hs.
      simpljoin1. eexists; eauto. 
    }
    simpljoin1.
    symbolic execution.
    destruct x6. 
    simpl; intro; tryfalse.
    destruct x6.
    pure_auto. 
    destruct x6. pure_auto. 
  }

  (* reason about loop body *) 
  apply disj_conj_distrib_pre.
  apply disj_rule.
  2: {
    eapply backward_rule1.
    eapply sep_aconj_r_aistrue_to_astar.
    introv Hsat.
    sep destruct Hsat.
    instantiate (1:=Vint32 Int.zero).
    instantiate (1:=Int32u).
    assert (exists p, x = Vptr p).
    { 
      sep_lifts_trms_in Hsat AEventNode.
      apply AEventNode_hd_vptr in Hsat.
      simpljoin1. eexists; eauto. 
    }
    simpljoin1.
    symbolic execution.
    destruct x6. simpl. pure_auto.
    destruct x6. simpl. pure_auto.
    destruct x6. simpl. pure_auto.
    hoare_split_pure_all.
    rename H4 into Hinjand.
    destruct Hinjand as (Hf & _).
    clear -Hf. false.
  }

  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  introv Hsat.
  sep destruct Hsat.  
  sep_lifts_trms_in Hsat (evsllseg x). 
  lets H00: evsllseg_tnptr_hdptr Hsat (ptr_isptr tn_addr); pauto.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  symbolic execution; pauto.
  destruct H3. 
  rewrite Int.eq_true.  
  destruct H00.
  subst. simpl. pure_auto.
  simpljoin1. simpl. destruct x4. simpl. pure_auto. 

  (* prepare to reason about "p1 ′ =ₑ p ′ .. OSEventListPtr;ₛ" *) 
  hoare_split_pure_all.
  hoare_lifts_trms_pre (evsllseg v'2).
  apply hoare_pure_gen with (p:=(isptr v'2)).
  introv Hsat.
  apply astar_r_aemp_intro in Hsat. 
  lets H00: evsllseg_tnptr_hdptr Hsat.
  apply H00.
  apply ptr_isptr.
  hoare_split_pure_all. 
  assert (Hptr: exists x, v'2 = Vptr x).
  {
    simpljoin1. destruct H5. subst. tryfalse. auto. 
  }
  destruct Hptr; substs.
  simpljoin1.
  eapply hoare_pure_gen; intros.
  eapply evsllseg_has_node'; eauto.
  hoare_split_pure_all.
  destruct H as (ectr & ectrl' & en & enl' & H'). 
  simpljoin1.
  unfold evsllseg at 2; fold evsllseg.
  unfold AEventNode at 1. 
  unfold AOSEvent at 2.
  unfold node at 1.  
  destruct ectr; destruct p.
  hoare_split_pure_all.
  destruct H as (Heqvp & Hmt).
  inverts Heqvp.
  assert(exists v1 v2 v3 v4 v5 v6 tail, v0 = v1::v2::v3::v4::v5::v6::tail).
  { apply struct_type_vallist_match_os_event; auto. }
  simpljoin1. 
  (* p1 ′ =ₑ p ′ .. OSEventListPtr;ₛ *)
  hoare forward.

  (*L9: if(p1 != pevent) *)
  match goal with H: V_OSEventListPtr _ = _ |- _ => inverts H end.
  hoare_lifts_trms_pre (evsllseg v'2).
  eapply hoare_pure_gen.
  introv Hsat.
  apply astar_r_aemp_intro in Hsat; eapply evsllseg_tnptr_hdptr in Hsat; eauto. 
  hoare forward; pauto.
  apply isptr_val_inj_vundef; auto.  

  (*L10: p = p1;*) 
  hoare forward.
  pauto.
  
  (*L11: x = 1; *) 
  hoare forward.
    
  (* establish loop invariant after loop body *)
  get_hsat Hsat.
  destruct Hsat.
  
  (*1: the case of os_code_defs.x=0 *)
  left. 
  eexists.
  exists (v'3 ++ ((x :: v'6 :: x1 :: x2 :: x3 :: v'2 :: x5, v1, v) :: nil)).
  exists (v'4 ++ (en :: nil)).
  exists ectrl'.
  exists enl'.
  sep pauto.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel A_dom_lenv.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat (evsllseg vhd).
  destruct x5; inverts H12 (* V_OSPostEventGrp ... = ... *). 

  eapply evsllseg_append1; eauto.
  
  get_hsat Hsat. 
  {
    split.
    2: {
      sep_lifts_trms_in Hsat (evsllseg v'2).
      apply evsllseg_hd_not_null in Hsat.
      auto. 
    }
    eapply nval_inj_neqz_neqptr; eauto. 
  }

  (* ptr_in_ectrls ... = false *) 
  casetac v'3 (nil : list os_inv.EventCtr) Hlnil Hlnnil.
  (* v'3 is nil *)
  subst.
  simpl.
  apply ptr_in_ectrls_singleton_false. 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (evsllseg vhd).
    apply evsllseg_tnptr_hdptr in Hsat; auto.
  }
  apply ptr_isptr.
  auto.
  eapply nval_inj_neqz_neqptr; eauto.
  (* v'3 is not nil *) 
  eapply ptr_in_ectrls_false_append; eauto.    
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg vhd).
  apply evsllseg_get_last_eq_p in Hsat; auto. 

  split.
  rewrite <- list_cons_assoc; auto. 
  rewrite <- list_cons_assoc; auto. 

  (* 2: the case of os_code_defs.x=1 *)
  right.
  get_hsat Hsat. 
  sep normal in Hsat.
  sep_lifts_trms_in Hsat Apure.
  apply sep_pure_split in Hsat; destruct Hsat.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat Apure.
  apply sep_pure_split in Hsat; destruct Hsat.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat Apure.
  apply sep_pure_split in Hsat; destruct Hsat.  
  rename H14 into Hinjor'. 
  assert (v'2 = Vptr tn_addr).
  {
    clear -Hinjor' H.
    casetac v'2 (Vptr tn_addr) Ht Hf. 
    auto.
    destruct H. subst. simpl in *.
    destruct tn_addr. simpl in Hinjor'. destruct Hinjor'; tryfalse.
    simpljoin1.
    simpl in Hinjor'. 
    destruct x; destruct tn_addr.
    destruct peq.
    subst.
    destruct (Int.eq i i0) eqn: Ei.
    asserts_rewrite (i = i0).
    apply int_eq_true_eq in Ei. auto.
    auto.
    simpl in Hinjor'. destruct Hinjor'; tryfalse.
    simpl in Hinjor'. destruct Hinjor'; tryfalse.
  }
  subst v'2.

  get_hsat Hsat. 
  assert (ectrl' = nil /\ enl' = nil).
  {
    sep_lifts_trms_in Hsat (evsllseg (Vptr tn_addr), AOSEvent (Vptr tn_addr)).
    lets H00: evsllseg_eq_hd_tn_node_nil Hsat; auto. 
  }
  destruct H14. subst ectrl'. subst enl'.
  unfold evsllseg at 1 in Hsat.
  sep_lifts_trms_in Hsat Apure.
  apply sep_pure_split in Hsat; destruct Hsat.
  get_hsat Hsat. 
  eexists. exists (x :: v'6 :: x1 :: x2 :: x3 :: Vptr tn_addr :: x5).
  exists v1. exists v.
  sep pauto.
  sep cancel Aop.
  sep cancel evsllseg.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel A_dom_lenv.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  sep pauto.
  eauto.
  go.
  eauto.
  go.
  split; auto.


  (*after the while loop, pre-cond is conj of the loop inv and the falsehood of the while condition *)
  apply disj_conj_distrib_pre.
  apply disj_rule.
  (*the case of x=0*)
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  intros.
  get_hsat Hsat. sep destruct Hsat.
  sep_lifts_trms_in Hsat (evsllseg x).
  lets H00: evsllseg_tnptr_hdptr Hsat.
  assert (Hptr: isptr x).
  { apply H00. apply ptr_isptr. } 
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  symbolic execution; pauto.
  rewrite Int.eq_true. 
  simpl.
  destruct H3.
  destruct Hptr. subst x. tryfalse.
  destruct H4 as (p & Hx). subst x.
  simpl. destruct p; simpl.
  pure_auto. 
  
  hoare_split_pure_all.
  destruct H4; tryfalse.

  (*the case of x=1*)
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.zero).
  introv Hsat. 
  sep destruct Hsat.
  assert (exists p, x = Vptr p).
  {
    sep_lifts_trms_in Hsat AEventNode.
    apply AEventNode_hd_vptr in Hsat.
    simpljoin1.
    eexists; eauto.     
  }
  simpljoin1.
  symbolic execution.
  destruct x6; pauto.
  destruct x6; pauto.
  destruct x6; pauto.
  
  (*L12: if (x == 1)*)
  hoare_split_pure_all.
  rewrite HeqH.
  unfold AEventNode.
  unfold AOSEvent at 2 3.
  unfold node.
  hoare_split_pure_all.
  simpljoin1. 
  assert(exists v1 v2 v3 v4 v5 v6 tail, v'3 = v1::v2::v3::v4::v5::v6::tail). 
  { apply struct_type_vallist_match_os_event; auto. }
  simpljoin1; auto.

  eapply seq_rule.
  eapply ift_rule''.
  instantiate (2:=Int32u).
  instantiate (1:=Vint32 Int.one).
  intros.
  symbolic execution.
  
  (*L13: p->OSEventListPtr = p1->OSEventListPtr;*)
  match goal with H: Vptr tn_addr = Vptr _ |- _ => inverts H end.
  hoare forward.
  assert(Hex: exists v1 v2 v3 v4 v5 v6 tail, osevent = v1::v2::v3::v4::v5::v6::tail).
  { apply struct_type_vallist_match_os_event; auto. }
  destruct Hex as (va & vb & vc & vd & ve & vf & tl & H').
  rewrite H'.
  simpl. lia. 

  (*L14: return*)
  assert(Hex: exists v1 v2 v3 v4 v5 v6 tail, osevent = v1::v2::v3::v4::v5::v6::tail).
  { apply struct_type_vallist_match_os_event; auto. }
  destruct Hex as (va & vb & vc & vd & ve & vf & tl & H').
  rewrite H' in *. clear H'.  
  do 2 (match goal with H: V_OSEventGrp _ = Some _ |- _ => inverts H end).
  apply disj_rule.
  2: { 
    hoare_split_pure_all.
    destruct H; tryfalse.
  }
  Ltac hoare_change pos asrt :=
    hoare lift pos%nat pre; apply backward_1 with (P':=asrt); sep pauto.
  hoare_change 12%nat (AEventData (x :: v'13 :: x1 :: x2 :: x3 :: vf :: x5) v'6).
  
  apply ret_rule'.
 
  introv Hsat.
  sep normal.  
  match goal with
    H: V_OSEventListPtr _ = Some _ |- _ => inverts H
  end.

  destruct x5.
  unfold V_OSPostEventGrp in H17; simpl in H17.
  tryfalse.
  inverts H17. 
  sep_lifts_trms_in Hsat (evsllseg vhd, Astruct (v'16, Int.zero), AOSEventTbl v'12, AOSPostEventTbl v'14, AEventData).
  eapply evsllseg_append1_frm in Hsat; eauto. 
  2: {
    clear -H19 H20.
    unfold struct_type_vallist_match in *.
    unfold OS_EVENT in *.
    simpl in *.
    simpljoin1.
    splits; eauto. 
  }

  sep pauto.
  sep cancel evsllseg.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel A_dom_lenv.
  sep cancel p_local.
  unfold AOSEvent.
  unfold node.
  sep pauto. 
  inverts H5.
  sep cancel Astruct.
  sep cancel AOSEventTbl.
  sep cancel AOSPostEventTbl.
  eauto.
  go.
  eauto.
  eauto.
  go.
  eauto.
  splits; auto.
  4: { eauto. }
  splits.
  {
    introv Hf.
    apply app_eq_nil in Hf.
    simpljoin1.
    clear -H26. tryfalse.
  }
  {
    introv _.
    splits; auto.     
    rewrite get_last_get_last_ptr_eq.
    symmetry.
    apply get_last_app.
    unfolds. unfolds.
    simpl; auto.
    rewrite upd_last_ectrls_last. auto. 
  }
  go.
  go.
  
Qed.   

