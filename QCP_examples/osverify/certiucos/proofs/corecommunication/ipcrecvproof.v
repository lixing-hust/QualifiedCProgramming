Require Import ucos_include.
Require Import Lia.

Require Import sem_lab.
Require Import ternary_assignment.

Require Import aux_pureLib.
Require Import corecommu_rules.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.
Require Import abs_op_corecommu_rules.
Require Import ipcrecv_rules.
Require Import corecommu_SemPtr_assign_rules.
Require Import evaux_pure.

Open Scope code_scope.

Open Scope int_scope.

Theorem cast_rv_tint32_tint16 :
  forall s e v v',
    s |= Rv e @ Tint32 == (Vint32 v) ->
    cast_eval v Tint32 Tint16 = Some v' ->
    s |= Rv (ecast e (Tint16)) @ (Tint16) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  auto.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Definition RLH_BROAD_P' z bvl bstack :=
  ( z = 0 /\ bstack = nil ) \/
  (0 < z  /\
  exists topv bstack', rev (firstn (Z.to_nat z) bvl)  = topv :: bstack' /\ 
  bstack = map unsigned2nat (topv::bstack')).
Lemma RLH_BROAD_P2RLH_BROAD_P' : forall z bvl bstack,
  0 <= z <= CORENUM ->  length bvl = 8%nat ->
  RLH_BROAD_P z bvl bstack -> RLH_BROAD_P' z bvl bstack.
Proof.
  intros.
  destruct H.
  apply Zle_lt_or_eq in H as [? | ?].
  - right. split;auto.
    unfold RLH_BROAD_P in H1.
    destruct H1 as [? [? ?]].
    assert (Z.to_nat z = S (Z.to_nat (z - 1)))%nat by lia.
    rewrite H4 in *.
    destruct bvl;try discriminate.
    simpl in *.
    destruct x. 
    { exfalso. eapply app_cons_not_nil;eauto. }
    rewrite H1.
    do 2 eexists.
    split;eauto.
  - subst z.
    unfold RLH_BROAD_P in H1.
    destruct H1 as [? [? ?]].
    left.  
    simpl in H.
    subst x.
    simpl in H1.
    split;auto.
Qed.

Lemma ipcrecv_split_coreheapl:
  forall coreheapl l m,
  In_heapl_addrval coreheapl l m ->
  forall P,
  AOScoreheapl coreheapl ** P
  ==>
  EX l1 l2 n vl1 vl2,
  [| coreheapl = l1 ++ (l, n, vl1 ++ vl2) :: l2 |] **
  AOScoreheapl (l1 ++ (get_off_addr l (Int.repr (Z.of_nat m)), (n - m)%nat, vl2) :: l2) **
  Aarray l (Tarray Tint8 m) vl1 **
  (* required when rebuilding the entire cheapl *)
  [| array_type_vallist_match Tint8 vl1 /\ (n <= (Z.to_nat HEAP_MAX_LENGTH ))%nat /\ 
    (length vl1 + length vl2 = n)%nat |] ** P.
Proof.
  intros.
  eapply In_heapl_addrval_split in H0; [ | apply H].
  sep destruct H0.
  sep split in H0.
  destruct H1; subst coreheapl.
  assert (In (l, x1, x2 ++ x3) (x ++ (l, x1, x2 ++ x3) :: x0)) by (apply in_elt).
  eapply AOScoreheapl_length_frm in H0;eauto.
  sep split in H0.
  eapply split_coreheapl with (m:=m) in H0; auto.
  sep split in H0.
  destruct H4. 
  rewrite <- H3 in H5.
  rewrite app_length in H3. symmetry in H3.
  sep auto.
Qed.

Lemma ipcsend_AOSIPCMem_merge : 
  forall pl memlls P corei step p memls meml,
  (corei < 8)%nat ->
  (step < 7)%nat -> 
  isvptr_list pl -> length pl = 8%nat -> length memlls = 8%nat ->
  nth_val' corei pl = Vptr p ->  nth_error memlls corei = Some memls -> length memls = 7%nat ->
    nth_error memls step = Some meml ->
  Memory_Node step p meml ** Memory_sigcore_aux_rm step O p memls **
  AOSIPCMem_aux_rm corei pl memlls **  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl  ** P ==> 
  AOSIPCMem pl memlls ** P.
Proof.
  intros.
  eapply AOSIPCMem_merge;eauto.
  sep auto.
Qed.

Definition IPCInfoList := (V$ CORE0_IPC :: V$ CORE1_IPC :: V$ CORE2_IPC :: V$ CORE3_IPC 
:: V$ CORE4_IPC:: V$ CORE5_IPC :: V$ CORE6_IPC :: V$ CORE7_IPC :: nil).

Ltac case_ipcinfo_true_asrt Htrue:=
  match goal with 
  | H: val_inj (if Int.eq ($ DNUM) ($ ?z) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <> Vint32 Int.zero  |- _ => assert (Int.eq ($ DNUM) ($ z) = true) as Htrue;[clear - H; destruct (Int.eq ($ DNUM) ($ z));auto | ]
  end.

Ltac generateipc_case n z h1 h2 rv:= 
hoare normal pre;
repeat (apply ex_intro_rule; intros);
pure intro;
let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
case_ipcinfo_true_asrt Hinteq;
assert (Z.to_nat DNUM = n)%nat as Hdnumeq;
[ clear - Hinteq h1 h2; apply Inteq_true_is_Zeq in Hinteq;
repeat progress (rewrite Int.unsigned_repr in Hinteq by mauto);lia | ];
let Hipc := fresh "H" in match goal with 
| |- context [LV ipcinfo @ _  |-> ?IPCN]=> assert (IPCN = nth_val' (Z.to_nat DNUM) IPCInfoList) as Hipc;
[ rewrite Hdnumeq;unfold IPCInfoList;auto | ];rewrite Hipc;
hoare abscsq;[apply noabs_oslinv 
| eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ];
unfold IPCINFO_case; rewrite Nat.eqb_refl;
eapply forward_rule2; [ eapply generateipc_rule ;[ | unfold p_local, CurLINV; sep auto];
erewrite Z2Nat.id in *;[ |apply Int.unsigned_range];
erewrite Int.repr_unsigned;
let s:= fresh "s" in let Hs := fresh "Hs" in intros s Hs;apply aconj_intro;[symbolic_execution;auto
| unfold IPCInfoList; rewrite Hdnumeq in Hs;symbolic_execution ]  |
let s:= fresh "s" in let Hs := fresh "Hs" in intros s Hs;eexists rv; sep auto ] end.

Ltac case_ipcinfo_false_asrt :=
  repeat progress (match goal with 
  | H: val_inj (if Int.eq ($ DNUM) ($ ?z) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vint32 Int.zero \/ val_inj (if Int.eq ($ DNUM) ($ ?z) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vnull  |- _ => assert (Int.eq ($ DNUM) ($ z) = false);[clear - H; destruct (Int.eq ($ DNUM) ($ z));auto;cbn in *;destruct H;tryfalse | ];clear H
  end).

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Lemma ipcrecv_absinfer_before_pend_succ:
  forall (sch:ossched) (P:asrt) x0  tid v aop,
    get v tid = Some (Vnull, Vnull, Vnull) ->
    can_change_aop P ->
      sch
      ⊢  <||
        ipcsend_before_pend' (|Vptr x0 :: nil|);; aop
        ||>  ** HCurTCB tid ** HEvPtr v ** P
      ⇒  <|| aop
        ||>  **
        HCurTCB tid **
        HEvPtr (set v tid (Vnull, Vptr x0, Vnull)) ** P.
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (q:= HCurTCB tid **
    HEvPtr (set v tid (Vnull, Vptr x0, Vnull)) ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    eapply absinfer_prim.
    can_change_aop_solver.
    can_change_aop_solver.
    unfolds;intros.
    eexists;exgamma.
    splits.
    { assert (get O evptrid = Some (evptr v)).
      { sep remember (3::nil)%nat in H1.
        simpl_sat H1;simpljoin1.
        eapply join_sig_get;eauto. }
      simpl_subst_gamma.
      hmstep_call_consturctor.
      eapply spec_prim_step.
      4: eapply map_join_emp.
      { unfold ipcsend_before_pend'.
        do 5 eexists.
        splits;eauto.
        sep remember (1::nil)%nat in H1.
        simpl_sat H1;simpljoin1.
        eapply join_sig_get;eauto. 
      }
      eapply abst_get_set_eqdom;eauto.
      simpl;auto.
      eapply tidsame_set;auto.
      eapply map_join_emp.
      hmstep_call_consturctor. 
    }
    destruct s as [[[[[? ?] ? ] ? ] ?] ?].
    simpl_sat H1;simpl_sat_goal.
    simpljoin1.
    cbn [getabsop gettaskst emptaskst] in *.
    simpljoin1.
  
    do 6 eexists.
    splits;eauto.
    instantiate (2:= empenv).
    { eapply join_comm.
    eapply map_join_emp. }
    instantiate (2:= empenv).
    { eapply join_comm.
    eapply map_join_emp. }
    cbn;splits;auto.
    unfold emposabst;auto.
  
    do 6 eexists.
    splits;eauto.
    (* instantiate (2:= empenv). *)
    eapply join_comm.
    eapply map_join_emp.
    instantiate (1:= set x10 evptrid (evptr (set v tid (Vnull, Vptr x0, Vnull)))).
    eapply join_set_r;eauto.
    unfold indom.
    eexists. eapply join_sig_get;eauto.
    
    do 6 eexists.
    splits;eauto.
    eapply join_comm.
    eapply map_join_emp.
    eapply join_sig_set;eauto.
    sep auto.
  }
  eapply absinfer_seq_end.
  can_change_aop_solver.
  can_change_aop_solver.
  sep auto.
Qed.

Lemma ipcrecv_absinfer_after_pend_succ:
  forall (sch:ossched) (P:asrt) x0  tid v aop,
    get v tid = Some (Vnull, Vptr x0, Vnull) ->
    can_change_aop P ->
      sch
      ⊢  <||
        ipcsend_after_pend (|nil|);; aop
        ||>  ** HCurTCB tid ** HEvPtr v ** P
      ⇒  <|| aop
        ||>  **
        HCurTCB tid **
        HEvPtr (set v tid (Vnull, Vnull, Vnull)) ** P.
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (q:= HCurTCB tid **
    HEvPtr (set v tid (Vnull, Vnull, Vnull)) ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    eapply absinfer_prim.
    can_change_aop_solver.
    can_change_aop_solver.
    unfolds;intros.
    eexists;exgamma.
    splits.
    { assert (get O evptrid = Some (evptr v)).
      { sep remember (3::nil)%nat in H1.
        simpl_sat H1;simpljoin1.
        eapply join_sig_get;eauto. }
      simpl_subst_gamma.
      hmstep_call_consturctor.
      eapply spec_prim_step.
      4: eapply map_join_emp.
      { unfold ipcsend_after_pend.
        do 3 eexists.
        splits;eauto.
        sep remember (1::nil)%nat in H1.
        simpl_sat H1;simpljoin1.
        eapply join_sig_get;eauto. 
      }
      eapply abst_get_set_eqdom;eauto.
      simpl;auto.
      eapply tidsame_set;auto.
      eapply map_join_emp.
      hmstep_call_consturctor. 
    }
    destruct s as [[[[[? ?] ? ] ? ] ?] ?].
    simpl_sat H1;simpl_sat_goal.
    simpljoin1.
    cbn [getabsop gettaskst emptaskst] in *.
    simpljoin1.

    do 6 eexists.
    splits;eauto.
    instantiate (2:= empenv).
    { eapply join_comm.
    eapply map_join_emp. }
    instantiate (2:= empenv).
    { eapply join_comm.
    eapply map_join_emp. }
    cbn;splits;auto.
    unfold emposabst;auto.

    do 6 eexists.
    splits;eauto.
    (* instantiate (2:= empenv). *)
    eapply join_comm.
    eapply map_join_emp.
    instantiate (1:= set x10 evptrid (evptr (set v tid (Vnull, Vnull, Vnull)))).
    eapply join_set_r;eauto.
    unfold indom.
    eexists. eapply join_sig_get;eauto.
    
    do 6 eexists.
    splits;eauto.
    eapply join_comm.
    eapply map_join_emp.
    eapply join_sig_set;eauto.
    sep auto.
  }
  eapply absinfer_seq_end.
  can_change_aop_solver.
  can_change_aop_solver.
  sep auto.
Qed.

Lemma IPCrecvProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api IPCrecv ipcrecvapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api IPCrecv ipcrecvapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api IPCrecv = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  destruct v'. 
  (* logic vallist : nil*)
  hoare lift 6%nat pre.
  apply absabort_rule.
  (* logic vallist : v :: _ *)
  rename H1 into H0.
  rename H3 into H.
  rename H4 into H1.
  (* If (dstAddr ′ ==ₑ NULL ||ₑ ′ 1 >ₑ size ′
  ||ₑ size ′ >ₑ ′ IPC_STEP
  ||ₑ srcCore ′ >ₑ ′ CORENUM − ′ 1
  ||ₑ srcCore ′ ==ₑ ′ DNUM
  ||ₑ flag ′ >ₑ ′ IPC_BROAD) *)
  hoare forward;pauto.
  1,2,3,4,5: destruct H;[ | destruct H as [[a b] H]]; subst x1;
  destruct (Int.ltu i1 ($ 1)); 
  destruct (Int.ltu ($ IPC_STEP) i1);
  destruct (Int.ltu ($ CORENUM -ᵢ $ 1) i);
  destruct (Int.eq i ($ os_code_defs.DNUM));
  destruct (Int.ltu ($ IPC_BROAD) i0);cbn ;pauto.
  
  - (* condition true*)  
  pure intro.
  assert (x1 = Vnull \/ Int.ltu i1 ($ 1) = true \/ Int.ltu ($ IPC_STEP) i1 = true \/ Int.ltu ($ CORENUM -ᵢ $ 1) i = true \/ Int.eq i ($ os_code_defs.DNUM)  = true \/ Int.ltu ($ IPC_BROAD) i0 = true).
  { destruct H;[ | destruct H as [x H];destruct x]; subst x1;
  destruct (Int.ltu i1 ($ 1)); 
  destruct (Int.ltu ($ IPC_STEP) i1);
  destruct (Int.ltu ($ CORENUM -ᵢ $ 1) i);
  destruct (Int.eq i ($ os_code_defs.DNUM));
  destruct (Int.ltu ($ IPC_BROAD) i0); tauto. } 
  hoare abscsq.
  apply noabs_oslinv.
  apply IPCrecv_high_level_step_invalid;auto.
  can_change_aop_solver.
  hoare forward.
  - (*condition false *)
    hoare forward.
    pure intro.
    fold (ipcrecv_succ_ack (Vint32 i :: x1 :: Vint32 i1 :: Vint32 i0 :: v :: nil)).

    assert ( (exists p, x1 = Vptr p) /\ Int.ltu i1 ($ 1) = false /\ Int.ltu ($ IPC_STEP) i1 = false /\ Int.ltu ($ CORENUM -ᵢ $ 1) i = false /\ Int.eq i ($ os_code_defs.DNUM)  = false /\ Int.ltu ($ IPC_BROAD) i0 = false ).
    { destruct H;[ | destruct H as [x H];destruct x]; subst x1;
    destruct (Int.ltu i1 ($ 1)); 
    destruct (Int.ltu ($ IPC_STEP) i1);
    destruct (Int.ltu ($ CORENUM -ᵢ $ 1) i);
    destruct (Int.eq i ($ os_code_defs.DNUM));
    destruct (Int.ltu ($ IPC_BROAD) i0).
    assert (Int.ltu Int.zero Int.one = true) by pauto. 
    repeat progress (cbn in * || rewrite H in *).
    all : try (destruct H2;tryfalse).
    splits;eauto. }
    clear H2.
    destruct H3 as [[p H2_] [H2_0 [H2_1 [H2_2 [H2_3 H2_4]]]]].
    subst x1.
    (*abs op : choose second branch*)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_choice2;eauto.
    1,2: can_change_aop_solver.
    (*abs op step : assume ipcrecv_valid_vl*)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_seq; eauto.
    3: { eapply absinfer_assume;eauto. 
         1,2 : can_change_aop_solver.
         intros. simpl. tauto. }
    1,2 : can_change_aop_solver.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_seq_end;eauto.
    1,2: can_change_aop_solver.
    assert ( 1 <= Int.unsigned i1 <= IPC_STEP)%Z as [? ?].
    { clear -H2_0 H2_1.
      rewrite Intlt_false_is_Zge in *.
      unfold IPC_STEP in *.
      split.
      rewrite Int.unsigned_repr in H2_0;mauto.
      rewrite Int.unsigned_repr in H2_1;mauto. }
    assert (Int.unsigned i <= 7 )%Z.
    { clear - H2_2. unfold CORENUM in *.  
      assert ($ 8 -ᵢ $ 1 = $ 7) by pauto.
      rewrite H in *.
      rewrite Intlt_false_is_Zge in *. 
      rewrite Int.unsigned_repr in *;mauto. }
    (* IF (flag ′ !=ₑ ′ IPC_BROAD) *)
    hoare forward.
    1,2,3: pauto.
    { (* Branch : (flag ′ !=ₑ ′ IPC_BROAD) *)
      instantiate (1:= EX return_v,
      <||ipcrecv_memcpy (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|);;
      (ASSUME ipcrecv_nonack (Vint32 i0)
        ?? ipcrecv_succ_ack
            (Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil));;
      END Some return_v ||>  **
      [| Int.eq i0 ($ IPC_BROAD) = false /\ return_v  = (V$ OS_NO_ERR) \/ 
      Int.eq i0 ($ IPC_BROAD) = true /\ return_v  = v  |] **
      LV ipcinfo @ Int32u |-> v'3 **
      LV step @ Int32u |-> v'2 **
      (EX v, LV tmpsem @ OS_EVENT ∗ |-> v) **
      (EX v, LV IPCBroad_cur @ Int32u |-> v) **
      p_local OSLInv tid init_lg **
      LV flag @ Int8u |-> Vint32 i0 **
      LV size @ Int32u |-> Vint32 i1 **
      LV dstAddr @ (Int8u) ∗ |-> Vptr p **
      LV srcCore @ Int8u |-> Vint32 i **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr ** 
      EX ier, Aier ier **
      A_dom_lenv
        ((flag, Int8u)
          :: (size, Int32u)
            :: (dstAddr, (Int8u) ∗)
                :: (srcCore, Int8u)
                  :: (IPCBroad_cur, Int32u)
                      :: (tmpsem, OS_EVENT ∗)
                        :: (step, Int32u) :: (ipcinfo, Int32u) :: nil) ).
      pure intro.
      assert (Int.eq i0 ($ IPC_BROAD) = false).
      { clear - H5.
        destruct (Int.eq i0 ($ IPC_BROAD));auto.
        cbn in *. unfold Int.notbool in *.
        assert (Int.eq Int.one Int.zero = false) by pauto.
        rewrite H in *.  tryfalse. }
      (* abs op step : choose nonbroad *)
      hoare abscsq.
      apply noabs_oslinv.
      eapply absinfer_choice1;eauto.
      can_change_aop_solver.
      can_change_aop_solver.
      (* ENTER_CRITICAL;ₛ *)
      hoare forward prim.
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      hoare_split_pure_all'. (* 不把后条件的ex 实例化*)
      (* tmpsem ′ =ₑ IPCSem ′ [srcCore ′];ₛ *)
      rename v'20 into vpthattr.
      rename v'21 into vcspace.
      rename v'22 into v22. 
      rename v'23 into v23. 
      rename v'24 into v24. 
       
      unfold CoreCommuInv.
      unfold AOSIPCSem.
      hoare normal pre.
      pure intro.
      hoare lift 44%nat pre.
      hoare name lift Aop pre.
      hoare forward.
      {
        clear - H2_2 H4.
        destruct (Int.unsigned i <=? Byte.max_unsigned)%Z eqn:eq; auto.
        eapply Z.leb_gt in eq.
        unfold CORENUM in *; exfalso; mauto.
      }
      {
        eapply isptr_list_nth_ptr; eauto.
        clear - H4. unfold CORENUM in *; lia.
      }

      (* OSTCBCur ′ .. __OSTskSemPtr =ₑ tmpsem ′;ₛ *)
      unfold EvtInv.
      hoare normal pre.
      hoare_ex_intro.
      pure_intro.
      (* pure intro. *)
      hoare name lift p_local pre.
      hoare name lift A_dom_lenv pre.
      hoare lifts (26::28::nil)%nat pre.
      hoare name lift AOSTCBList pre.
      hoare lifts (2::1::5::3::4::nil)%nat pre.
      hoare name lift Aop pre.
      fold init_lg.
      assert(exists p, nth_val' (Z.to_nat (Int.unsigned i)) IPCSem_ptrl  = Vptr p /\ In (Vptr p) IPCSem_ptrl).
      {
        eapply isptr_list_nth_ptr_ex; eauto.
        lia.
      }
      destruct H19, H19; rewrite H19.
      eapply seq_rule.
      {
        apply SemPtr_assign_lv; auto.
      }

      pure intro.

      cbn [ipcrecv_before_pend_IPCSem].

      assert (nth_error OSIPCSem_val (Z.to_nat (Int.unsigned i)) = Some (x)).
      {
        pose proof nth_val'_imp_nth_val_vptr _ _ H19.
        (* Search (nth_val _ _ = Some _). *)
        pose proof nth_val_nth_error (Z.to_nat (Int.unsigned i)) IPCSem_ptrl (Vptr x).
        destruct H30.
        pose proof H30 H29.
        unfold IPCSem_ptrl in H32.
        (* Search (nth_error (map _ _) _ = Some _). *)
        destruct (nth_error OSIPCSem_val (Z.to_nat (Int.unsigned i))) eqn: H70.
        {
          pose proof map_nth_error (fun x : addrval => Vptr x) (Z.to_nat (Int.unsigned i)) OSIPCSem_val H70.
          simpl in H33.
          rewrite H32 in H33.
          inversion H33. f_equal.
        }
        {
          pose proof nth_error_None OSIPCSem_val (Z.to_nat (Int.unsigned i)).
          destruct H33.
          pose proof H33 H70.
          lia.
        }
      }
      rewrite H29.
      hoare name lift Aop curtid evptrid pre.
      hoare remember (1::2::3::nil)%nat pre.
      eapply abscsq_rule';
      [apply noabs_oslinv | | ].
      {
        eapply ipcrecv_absinfer_before_pend_succ; eauto.
        subst H30.
        can_change_aop_solver.
      }
      subst H30.

      unfold sempend_ipcsem.
      rewrite H29.

      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        unfold EvtInv, CoreCommuInv, AOSIPCSem, AOSMapTbl,
                AOSUnMapTbl, AOSTCBPrioTbl, AOSRdyTblGrp, AOSRdyTbl,
                AOSRdyGrp, AOSTime, AGVars.
        sep normal.
        sep eexists.
        sep autocancel.
        sep split.
        exact H30.
        all: try auto.
        eapply evdel_nodup_normal_semptr_preserve; eauto.
        eapply evcre_nodup_normal_semptr_preserve; eauto.
        3: eapply sem_ecb_p_semptr_normal_preserve; eauto.
        2: eapply mux_ecb_p_semptr_normal_preserve; eauto.
        1: eapply mq_ecb_p_semptr_normal_preserve; eauto.
        all: unfold CORESEM_INECB_P in H13.
        all: destruct H13, H31.
        all: unfold IPCSem_ptrl in H26.
        all: apply H13.
        all: pose proof in_map_iff (fun x : addrval => Vptr x) OSIPCSem_val (Vptr x).
        all: destruct H33.
        all: pose proof H33 H26.
        all: destruct H35 as [x1 [? ?]].
        all: inversion H35; subst x1; auto.
      }
      auto. good_frm_sovler.
      
      (* OSIPCSemPend (­tmpsem ′, ′ 0, &ₐ err ′­);ₛ *)
      eapply seq_rule.
      {
        eapply call_rule'.
        intuition eauto.
        4:{
          intros.
          unfold getasrt, OSSemPendPost, OSSemPendPost' in H30.
          do 6 destruct H30.
          exists (logic_val (V$ 1)
          :: logic_val (V$ os_code_defs.__EvLoc_normal)
              :: logic_val Vnull
                :: logic_val x4 :: logic_val Vnull :: nil).
          sep auto.
        }
        4:{
          intros.
          unfold getasrt, OSSemPendPre, OSSemPendPre' in H30.
          do 4 destruct H30.
          exists (logic_val (V$ 1)
          :: logic_val (V$ os_code_defs.__EvLoc_normal)
              :: logic_val Vnull
                :: logic_val x1 :: logic_val Vnull :: nil).
          sep auto.
        }
        2:{
          intros.
          unfold getasrt, OSSemPendPre, OSSemPendPre'.
          sep normal.
          exists (ipcrecv_after_pend (|nil|);;
          ipcrecv_memcpy
          (|Vint32 i
            :: Vptr p
               :: Vint32 i1 :: Vint32 i0 :: v :: nil|);;
          (ASSUME ipcrecv_nonack (Vint32 i0)
           ?? ipcrecv_succ_ack
                (Vint32 i
                 :: Vptr p
                    :: Vint32 i1 :: Vint32 i0 :: v :: nil));;
          END Some (V$ OS_NO_ERR)) (Vptr x) (V$ OS_NO_ERR) v'4.
          sep autocancel.
          sep pauto.
          2:{
            assert (nth_val 0 (Vptr x :: Vint32 Int.zero :: nil) = Some (Vptr x)).
            simpl; auto.
            rewrite -> H33; auto.
          }
          exact H30.
        }
        2: good_frm_sovler.
        2: auto.
        intros.
        apply rvl_elim.
        sep get rv.
        apply rvl_elim.
        2: apply rvl_nil.
        eapply cast_rv_tint32_tint16.
        symbolic_execution.
        auto.
      }

      unfold_funpost.
      hoare normal pre.
      pure intro.
      inversion H30; subst; clear H30.

      (* ENTER_CRITICAL;ₛ *)
      hoare forward prim.
      unfold EvtInv.
      hoare normal pre.
      pure intro.

      (* OSTCBCur ′ .. __OSTskSemPtr =ₑ NULL;ₛ *)
      hoare name lift Aop tcbllsegevaux AOSTCBList p_local A_dom_lenv pre.
      eapply seq_rule.
      apply SemPtr_assign_null; auto.
      pure intro.

      (* after_pend *)
      hoare name lift Aop curtid evptrid pre.
      eapply abscsq_rule'; [apply noabs_oslinv | | ].
      {
        eapply ipcrecv_absinfer_after_pend_succ; eauto.
        can_change_aop_solver.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        unfold EvtInv.
        sep normal.
        sep eexists.
        sep autocancel.
        sep split.
        exact H43.
        all: eauto.
        eapply evdel_nodup_set_null3_preserve; eauto.
        eapply evcre_nodup_set_null3_preserve; eauto.
        eapply mq_ecb_p_set_null3_preserve; eauto.
        eapply mux_ecb_p_set_null3_preserve; eauto.
        eapply sem_ecb_p_set_null3_preserve; eauto.
      }
      auto.
      good_frm_sovler.
      sep autocancel.
    }
    { (* Branch : (flag ′ ==ₑ ′ IPC_BROAD) *)
      instantiate (1:= EX return_v,
      <||ipcrecv_memcpy (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|);;
      (ASSUME ipcrecv_nonack (Vint32 i0)
        ?? ipcrecv_succ_ack
            (Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil));;
      END Some return_v ||>  **
      [|exists i, v= Vint32 i /\ Int.unsigned i <= 7 /\ Int.eq i ($ DNUM) = false|] **
      [| Int.eq i0 ($ IPC_BROAD) = false /\ return_v  = (V$ OS_NO_ERR) \/ 
      Int.eq i0 ($ IPC_BROAD) = true /\ return_v  = v  |] **
      LV ipcinfo @ Int32u |-> v'3 **
      LV step @ Int32u |-> v'2 **
      (EX v0, LV tmpsem @ OS_EVENT ∗ |-> v0) **
      (EX v0, LV IPCBroad_cur @ Int32u |-> v0) **
      p_local OSLInv tid init_lg **
      LV flag @ Int8u |-> Vint32 i0 **
      LV size @ Int32u |-> Vint32 i1 **
      LV dstAddr @ (Int8u) ∗ |-> Vptr p **
      LV srcCore @ Int8u |-> v **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr **
      EX ier, Aier ier **
      A_dom_lenv
        ((flag, Int8u)
          :: (size, Int32u)
            :: (dstAddr, (Int8u) ∗)
                :: (srcCore, Int8u)
                  :: (IPCBroad_cur, Int32u)
                      :: (tmpsem, OS_EVENT ∗)
                        :: (step, Int32u) :: (ipcinfo, Int32u) :: nil) ).
      pure intro.
      assert (Int.eq i0 ($ IPC_BROAD) = true).
      { clear - H5.
        destruct (Int.eq i0 ($ IPC_BROAD));auto.
        cbn in *. unfold Int.notbool in *.
        assert (Int.eq Int.zero Int.zero = true) by pauto.
        rewrite H in *. destruct H5;tryfalse. }
      (* abs op step : choose broad *)
      hoare abscsq.
      apply noabs_oslinv.
      eapply absinfer_choice2;eauto.
      can_change_aop_solver.
      can_change_aop_solver.
      (* ENTER_CRITICAL;ₛ *)
      hoare forward prim.
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      hoare_split_pure_all'. (* 不把后条件的ex 实例化*)
      rename v'20 into vpthattr.
      rename v'21 into vcspace.
      rename v'22 into v22. 
      rename v'23 into v23. 
      rename v'24 into v24. 
  
      (* tmpsem ′ =ₑ IPCSemShared ′;ₛ *)
      unfold CoreCommuInv.
      unfold AOSIPCSemShared.
      hoare normal pre.
      pure intro.
      hoare lift 45%nat pre.
      hoare name lift Aop pre.
      eapply seq_rule.
      {
        eapply assign_rule_lvar with (tp2:=Tptr OS_EVENT)
        (v2:=(Vptr OSSemShared_val)).
        {
          intros.
          split.
          intros; exact H14.
          sep auto.
        }
        2:{
          apply assign_type_match_true.
          simpl.
          auto.
        }
        2: sep auto.
        intros.
        symbolic_execution.
      }

      (* OSTCBCur ′ .. __OSTskSemPtr =ₑ tmpsem ′;ₛ *)
      unfold EvtInv.
      hoare normal pre.
      hoare_ex_intro.
      pure_intro.
      hoare name lift p_local pre.
      hoare name lift A_dom_lenv pre.
      hoare lifts (26::28::nil)%nat pre.
      hoare name lift AOSTCBList pre.
      hoare lifts (2::1::5::3::4::nil)%nat pre.
      hoare name lift Aop pre.
      fold init_lg.
      eapply seq_rule.
      apply SemPtr_assign_lv; auto.
      pure intro.

      unfold ipcrecv_before_pend_IPCSemShared.
      hoare name lift Aop curtid evptrid pre.
      hoare remember (1::2::3::nil)%nat pre.
      eapply abscsq_rule';
      [apply noabs_oslinv | | ].
      {
        eapply ipcrecv_absinfer_before_pend_succ; eauto.
        subst H23.
        can_change_aop_solver.
      }
      subst H23.
      
      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        unfold EvtInv, CoreCommuInv, AOSIPCSemShared, AOSMapTbl,
                AOSUnMapTbl, AOSTCBPrioTbl, AOSRdyTblGrp, AOSRdyTbl,
                AOSRdyGrp, AOSTime, AGVars.
        sep normal.
        sep eexists.
        sep autocancel.
        sep split.
        exact H23.
        all: try auto.
        eapply evdel_nodup_normal_semptr_preserve; eauto.
        eapply evcre_nodup_normal_semptr_preserve; eauto.
        3: eapply sem_ecb_p_semptr_normal_preserve; eauto.
        2: eapply mux_ecb_p_semptr_normal_preserve; eauto.
        1: eapply mq_ecb_p_semptr_normal_preserve; eauto.
        all: unfold CORESEM_INECB_P in H11.
        all: destruct H11, H24.
        all: apply H25.
      }
      auto. good_frm_sovler.

      (* OSIPCSemPend (-IPCSemShared ′, ′ 0 -);ₛ *)
      eapply seq_rule.
      {
        eapply call_rule'.
        intuition eauto.
        4:{
          intros.
          unfold getasrt, OSSemPendPost, OSSemPendPost' in H23.
          do 6 destruct H23.
          exists (logic_val (V$ 1)
          :: logic_val (V$ os_code_defs.__EvLoc_normal)
              :: logic_val Vnull
                :: logic_val x3 :: logic_val Vnull :: nil).
          sep auto.
        }
        4:{
          intros.
          unfold getasrt, OSSemPendPre, OSSemPendPre' in H23.
          do 4 destruct H23.
          exists (logic_val (V$ 1)
          :: logic_val (V$ os_code_defs.__EvLoc_normal)
              :: logic_val Vnull
                :: logic_val x0 :: logic_val Vnull :: nil).
          sep auto.
        }
        2:{
          intros.
          unfold getasrt, OSSemPendPre, OSSemPendPre'.
          sep normal.
          exists (ipcrecv_after_pend (|nil|) ;;
            ( ipcrecv_broad_error (|(Vint32 i::Vptr p::Vint32 i1::Vint32 i0::v::nil)|) ??
            ASSERT (ipcrecv_middelval v) ;;
            ipcrecv_broad (|(Vint32 i::Vptr p::Vint32 i1::Vint32 i0::v::nil)|);;
            (* memcpy *)
            ipcrecv_memcpy (|(Vint32 i::Vptr p::Vint32 i1::Vint32 i0::v::nil)|) ;; 
            (* ack or nonack *)
            (ASSUME (ipcrecv_nonack (Vint32 i0)) ?? 
            ipcrecv_succ_ack (Vint32 i::Vptr p::Vint32 i1::Vint32 i0::v::nil) ) ;;
            (* return value *)
            END (Some v))) (Vptr OSSemShared_val) (V$ OS_NO_ERR) v'4.
          sep autocancel.
          sep pauto.
          2:{
            assert (nth_val 0 (Vptr OSSemShared_val :: Vint32 Int.zero :: nil) = Some (Vptr OSSemShared_val)).
            simpl; auto.
            rewrite -> H26; auto.
          }
          unfold spec_code_cons.
          sep auto.
        }
        2: good_frm_sovler.
        2: auto.
        intros.
        apply rvl_elim.
        sep get rv.
        apply rvl_elim.
        2: apply rvl_nil.
        eapply cast_rv_tint32_tint16.
        symbolic_execution.
        auto.
      }

      unfold_funpost.
      hoare normal pre.
      pure intro.
      inversion H23; subst; clear H23.
      
      (* ENTER_CRITICAL;ₛ *)
      hoare forward prim.
      unfold EvtInv.
      hoare normal pre.
      pure intro.
      rename v'61 into vpthattr1.
      rename v'62 into vcspace1.
      rename v'63 into v63. 
      rename v'64 into v64. 
      rename v'65 into v65. 
      rename v'66 into v'61. 
      rename v'67 into v'62. 
      rename v'68 into v'63. 
      rename v'69 into v'64. 
      rename v'70 into v'65. 
      rename v'71 into v'66. 
      rename v'72 into v'67. 
      rename v'73 into v'68. 
      rename v'74 into v'69. 
      rename v'75 into v'70. 
      rename v'76 into v'71. 
      rename v'77 into v'72. 
      rename v'78 into v'73. 
      rename v'79 into v'74. 
      rename v'80 into v'75. 
      rename v'81 into v'76. 
      rename v'82 into v'77. 
      rename v'83 into v'78. 
      rename v'84 into v'79. 
      
      (* OSTCBCur ′ .. __OSTskSemPtr =ₑ NULL;ₛ *)
      hoare name lift Aop tcbllsegevaux AOSTCBList p_local A_dom_lenv pre.
      eapply seq_rule.
      apply SemPtr_assign_null; auto.
      pure intro.

      (* after_pend *)
      hoare name lift Aop curtid evptrid pre.
      eapply abscsq_rule'; [apply noabs_oslinv | | ].
      {
        eapply ipcrecv_absinfer_after_pend_succ; eauto.
        can_change_aop_solver.
      }
      
      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      {
        unfold EvtInv.
        sep normal.
        sep eexists.
        sep autocancel.
        sep split.
        exact H36.
        all: eauto.
        eapply evdel_nodup_set_null3_preserve; eauto.
        eapply evcre_nodup_set_null3_preserve; eauto.
        eapply mq_ecb_p_set_null3_preserve; eauto.
        eapply mux_ecb_p_set_null3_preserve; eauto.
        eapply sem_ecb_p_set_null3_preserve; eauto.
      }
      auto.
      good_frm_sovler.
      fold (ipcrecv_succ_ack (Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil)) in *.

      (* ENTER_CRITICAL;ₛ *)
      hoare forward prim.
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro. (* 不把后条件的ex 实例化*)
      rename v'94 into vpthattr2.  
      rename v'95 into vcspace2.
      rename v'96 into v96. 
      rename v'97 into v97. 
      rename v'98 into v98. 
    
      unfold CoreCommuInv, AOSIPCBroadList.
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro. (* 不把后条件的ex 实例化*)
      rename v'101 into broad_ptr.
      rename v'97 into broad_vl.
      rename v'96 into broad_stack.
      assert (Int.unsigned ($ broad_ptr) <=? Byte.max_unsigned = true).
      { 
        clear -H38 H48.
        unfold CORENUM in H48.
        mauto. cbn;lia. }
      
        
      unfold EvtInv, TmrInv, HeapInv'.
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.

      (* If (IPCBroad_pointer ′ ==ₑ ′ 0 ||ₑ IPCBroad_pointer ′ >ₑ ′ CORENUM) *)
      hoare forward.
      1,2,3,4,5: pauto.
      { (* broad_ptr illegal *) 
        pure intro.
        assert (Int.eq ($ broad_ptr) ($ 0) = true  \/ Int.ltu ($ CORENUM) ($ broad_ptr) = true ) by pauto.
        clear H54 H61 H62.
        apply RLH_BROAD_P2RLH_BROAD_P' in H40; auto.
        unfold RLH_BROAD_P' in H40.
        destruct H40 as  [[Hl Hb] | [Hl ?]].
        2: { destruct H63 as [H63 |H63].
             { false.
               clear -H63 Hl H48.
             apply Int_eq_dec in H63.
             apply int_unsigned_inj in H63.
             lia.
             cbn. unfold CORENUM in H48. lia. }
             { false. 
               clear -H63 Hl H48.
               apply Intlt_true_is_Zlt in H63.
               unfold CORENUM in *.
               do 2 rewrite Int.unsigned_repr in * by mauto.
               lia. } 
            } 
        { rewrite Hb.
          hoare name lift ipcbroadid pre.
          hoare name lift ipcsemshareid pre.
          hoare name lift ipcsendsemid pre.
          hoare name lift ipcsemid pre.
          hoare name lift ipcrecvid pre.
          hoare name lift ipcsendid pre.
          hoare name lift oscoreheapid pre.
          hoare name lift curcoreid pre.
          hoare name lift curtid pre.
          hoare name lift abstcblsid pre.
          hoare name lift absecblsid pre.
          hoare name lift Aop pre.

          (* abs op step : ipcbroad_error *)
          eapply abscsq_rule'.
          apply noabs_oslinv.
          eapply IPCrecv_high_level_step_broad_nil.
          eauto.
          can_change_aop_solver.

          (* EXIT_CRITICAL;ₛ *)
          hoare forward prim.
          {
            unfold EvtInv, TmrInv, HeapInv', CoreCommuInv, AOSIPCBroadList.
            sep normal.
            sep eexists.
            sep autocancel.
            sep split.
            sep auto.
            all: try auto.
            unfold RLH_BROAD_P; eexists; split; eauto.
          }
          auto. good_frm_sovler.

          (* RETURN ′ EBUSY *)
          hoare forward.
        }
      }
    hoare forward.
    (* broad_ptr legal *) 
    pure intro.
    assert (Int.eq ($ broad_ptr) ($ 0) = false /\ Int.ltu ($ CORENUM) ($ broad_ptr) = false) as [? ?].
    { clear -H54. 
      assert (Int.ltu Int.zero Int.one = true) by pauto.
      destruct (Int.eq ($ broad_ptr) ($ 0)); destruct (Int.ltu ($ CORENUM) ($ broad_ptr)); auto.
      1,2,3: cbn in H54;
      rewrite H in *; cbn in H54; destruct H54;tryfalse. }
    clear H54.

    (* −− IPCBroad_pointer ′;ₛ *)
    hoare forward.
    pauto.

    (* IPCBroad_cur ′ =ₑ IPCBroad_Core_Current ′ [IPCBroad_pointer ′];ₛ *)
    assert ( broad_ptr >= 1).
    { clear - H38 H61 H48.
      apply Inteq_false_is_Zneq in H61.
      unfold CORENUM in *.
      do 2 rewrite Int.unsigned_repr in * by (cbn;lia).
      lia. }
    assert ( broad_ptr <= 8).
    { clear -H38 H48 H62.
      apply Intlt_false_is_Zge in H62.
      unfold CORENUM in *.
      do 2 rewrite Int.unsigned_repr in * by (cbn;lia).
      lia. }
    assert (Int.unsigned ($ broad_ptr -ᵢ $ 1) = broad_ptr - 1).
    { assert ($ broad_ptr -ᵢ $ 1 = $ (broad_ptr - 1)%Z).
      { rewrite Int.sub_signed.
      do 2 rewrite Int.signed_repr by (cbn;lia).
      auto. } 
      rewrite H64.
      clear -H54 H63 H48.
      unfold CORENUM in *.
      rewrite Int.unsigned_repr in * by (cbn;lia).
      auto. }
    hoare forward.
    { rewrite H64. clear -H48. unfold CORENUM in *.
      assert (broad_ptr - 1 <=? Byte.max_unsigned  = true) by (cbn;lia).
      rewrite H;auto. }
    { rewrite H64.
      eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match;eauto.
      rewrite H46.
      clear - H63 H54.
      lia. }
    assert (rule_type_val_match Int32u (nth_val' (Z.to_nat (Int.unsigned ($ broad_ptr -ᵢ $ 1))) broad_vl) = true).
    { eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match;eauto.
    lia. }
    destruct (nth_val' (Z.to_nat (Int.unsigned ($ broad_ptr -ᵢ $ 1))) broad_vl) eqn : ?;tryfalse.
    (* clear H33. *)

    (* srcCore ′ =ₑ IPCBroad_cur ′;ₛ *)
    hoare forward.

    (* IPCBroad_Core_Current ′ [IPCBroad_pointer ′] =ₑ ′ (-1);ₛ *)
    hoare forward.
    { assert (Int.unsigned ($ broad_ptr -ᵢ $ 1) <=? Byte.max_unsigned = true)%Z by (cbn;lia).
      rewrite H67. auto. }
    rewrite H64.

    (* broad stack*)
    apply RLH_BROAD_P2RLH_BROAD_P' in H40; auto.
    unfold RLH_BROAD_P' in H40.
    destruct H40 as  [[Hl Hb] | [? [? [? [? ?]]]]]. 
    { false.  lia. }
    assert (x = Vint32 i2).
    { apply nth_val'_imply_nth_val in Heqv0;[ |rewrite H64;lia].
      erewrite nth_val_nth_error in Heqv0.
      rewrite H64 in Heqv0.
      eapply revfirstn_nth_error;eauto.
      assert ((Z.to_nat (broad_ptr - 1) + 1) = (Z.to_nat broad_ptr))%nat by lia.
      rewrite H68. eauto. } 
    subst x.
    (* abs op step : assert ipcrecv_middelval *)
    assert (v <> (Vint32 i2) \/ v = Vint32 i2) as Hasrt by tauto.
    destruct Hasrt as [Hasrt | Hasrt].
    (* v <> (Vint32 i2) *)
    {
    hoare name lift ipcbroadid pre.
    hoare name lift ipcsemshareid pre.
    hoare name lift ipcsendsemid pre.
    hoare name lift ipcsemid pre.
    hoare name lift ipcrecvid pre.
    hoare name lift ipcsendid pre.
    hoare name lift oscoreheapid pre.
    hoare name lift curcoreid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift absecblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply IPCrecv_high_level_step_broad_assert_abt;eauto.
    can_change_aop_solver.
    apply absabort_rule. }
    (* v = (Vint32 i2) *)
    subst v.
    hoare name lift ipcbroadid pre.
    hoare name lift ipcsemshareid pre.
    hoare name lift ipcsendsemid pre.
    hoare name lift ipcsemid pre.
    hoare name lift ipcrecvid pre.
    hoare name lift ipcsendid pre.
    hoare name lift oscoreheapid pre.
    hoare name lift curcoreid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift absecblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply IPCrecv_high_level_step_broad_assert_cont;eauto.
    can_change_aop_solver.
    (* abs op step : ipcrecv_broad *)
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply IPCrecv_high_level_step_broad;eauto.
    can_change_aop_solver.

    (* EXIT_CRITICAL *)
    eapply forward_rule2.
    { hoare forward prim. 
      unfold EvtInv, TmrInv, HeapInv', CoreCommuInv, AOSIPCBroadList.
      sep normal.
      sep eexists.
      sep autocancel.
      sep split.
      exact H68.
      all: try auto.
      { (* RLH_BROAD_P*)
        (* clear H35. *)
        assert ((Int.unsigned ($ broad_ptr) - Int.unsigned ($ 1)) = broad_ptr -1)%Z.
        { clear -H64 H54 H63 H40. mauto. }
        rewrite H67.
        unfold RLH_BROAD_P.
        rewrite firstn_update_nth_val.
        remember (8 - (Z.to_nat broad_ptr))%nat as m.
        assert ( (Z.to_nat broad_ptr) = (length broad_vl) - m)%nat by lia.
        rewrite H69 in H66. 
        (* clear H35. *)
        assert ( Z.to_nat (broad_ptr -1) = (length broad_vl) - (m + 1))%nat by lia.
        rewrite H70.
        (* clear H35. *)
        erewrite <- skipn_rev in *.
        apply skipn_stack in H66.
        eexists.
        split;eauto.
      }
      { splits.
        eapply array_type_vallist_match_hold;[auto | lia |cbn;auto ].
        rewrite update_nth_val_len_eq;auto.
        unfold legal_broadlist.
        do 2 erewrite Int.unsigned_repr by (cbn;lia).
        erewrite firstn_update_nth_val.
        unfold legal_broadlist in H47.
        eapply Forall_firstn_lt;eauto.
        assert ((S (Z.to_nat (broad_ptr - 1))) =  (Z.to_nat broad_ptr)) by lia.
        rewrite H67.
        auto. }
      do 2 erewrite Int.unsigned_repr by (cbn;lia). lia.
      good_frm_sovler. }
      (* 1,2: eauto.
      pauto. } *)
      intros.
      exists (Vint32 i2).
      sep auto.
      eexists. split;eauto.
      unfold legal_broadlist in H47.
      apply nth_val'_imply_nth_val in Heqv0; [ |rewrite H64;lia].
      rewrite H64 in Heqv0.
      eapply nth_val_In_firstn in Heqv0.
      assert ((Z.to_nat (broad_ptr - 1) + 1) = (Z.to_nat broad_ptr))%nat by lia.
      rewrite H67 in Heqv0.
      eapply Forall_forall in H47;eauto.
      unfold legal_broad_element in H47. clear -H47.
      destruct H47 as [? [? ?]].
      simpl_intltbool.
      erewrite Int.signed_eq_unsigned in H0. split; [lia | auto].
      eapply Int.signed_positive. lia.
    }
    eapply backward_rule1.
    { instantiate (1:=EX return_v,
    <||ipcrecv_memcpy (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|);;
    (ASSUME ipcrecv_nonack (Vint32 i0)
      ?? ipcrecv_succ_ack
          (Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil));;
    END Some return_v ||>  **
    [| Int.eq i0 ($ IPC_BROAD) = false /\ return_v  = (V$ OS_NO_ERR) \/ 
    Int.eq i0 ($ IPC_BROAD) = true /\ return_v  = v  |] ** 
    LV ipcinfo @ Int32u |-> v'3 **
    LV step @ Int32u |-> v'2 **
    (EX v0 : val, LV tmpsem @ OS_EVENT ∗ |-> v0) **
    (EX v0 : val, LV IPCBroad_cur @ Int32u |-> v0) **
    p_local OSLInv tid init_lg **
    LV flag @ Int8u |-> Vint32 i0 **
    LV size @ Int32u |-> Vint32 i1 **
    LV dstAddr @ (Int8u) ∗ |-> Vptr p **
    (EX i3, LV srcCore @ Int8u |-> Vint32 i3 ** 
     [| Int.eq i0 ($ IPC_BROAD) = false /\ i3 = i \/ Int.eq i0 ($ IPC_BROAD) = true /\ 
     (exists i2, i3 = i2 /\ v = Vint32 i2 /\ Int.unsigned i2 <= 7 /\ Int.eq i2 ($DNUM) = false )
        |])**
    Aie true **
    Ais nil **
    Acs nil **
    Aisr empisr **
    EX ier, Aier ier **
    A_dom_lenv
      ((flag, Int8u)
        :: (size, Int32u)
          :: (dstAddr, (Int8u) ∗)
              :: (srcCore, Int8u)
                :: (IPCBroad_cur, Int32u)
                    :: (tmpsem, OS_EVENT ∗) :: (step, Int32u) :: (ipcinfo, Int32u) :: nil)).
    intros.
    destruct H5.
    { sep normal in H5. sep destruct H5. sep split in H5.
      destruct H6 as [[? ?] | [H6 ?]];[ subst x | rewrite H6 in H7 ]. 
      2:{ cbn in H7;unfold Int.notbool in H7. clear - H7. exfalso.
          assert (Int.eq Int.one Int.zero = false) by pauto.
          rewrite H in H7. destruct H7. contradiction. }
      exists (V$ OS_NO_ERR).
      sep auto.  }
    { sep normal in H5. sep destruct H5. sep split in H5. 
      destruct H7 as [[H7 ?] | [H7 ?]];[ rewrite H7 in H8| subst x].
      { exfalso. cbn in H8;unfold Int.notbool in H8. 
        clear - H8.  assert (Int.eq Int.zero Int.zero = true) by pauto.
        rewrite H in H8. destruct H8;discriminate.  }
      exists v.
      destruct H6 as [? [? [? ?]]]; subst v.
      sep auto. 
      right.
      split. 
      clear -H8. destruct (Int.eq i0 ($ IPC_BROAD));auto.
        cbn in *. unfold Int.notbool in *.
        assert (Int.eq Int.zero Int.zero = true) by pauto.
        rewrite H in *. destruct H8;tryfalse.
      eexists;split;eauto.  } 
    }
    hoare normal pre.
    pure intro.
    assert ((if Int.unsigned v'8 <=? Byte.max_unsigned then true else false) = true) .
    { destruct H5 as [[? ?] | [? [? [? [? ?]]]]];subst v'8;pauto.
      assert (Int.unsigned x <= 255) by lia. pauto. }
    
      (* IF (srcCore ′ >ₑ ′ DNUM)
      {step ′ =ₑ srcCore ′ − ′ 1}
      ELSE {step ′ =ₑ srcCore ′};ₛ *)
    eapply seq_rule.
    eapply wzy_if_else_rule;
      [symbolic_execution;try pauto|  |
        reflexivity | | ];
      [symbolic_execution;try pauto|
        hoare forward | hoare forward]. 
        { instantiate (1:= Int.unsigned v'8). rewrite Int.repr_unsigned. auto. }
        { match goal with
        | |- _ ?v => instantiate (1:=fun vx => vx = v)
        end; simpl; auto. }
    pose proof dnum_range as Hdnum.
    destruct Hdnum as [Hdnum_ge Hdnum_le].
    pure intro.
    rename v'10 into stepz.
    assert (0 <= stepz < 7)%Z as [Hstepz_ge Hstepz_lt].
    { clear - H8 H5 H4 H2_4 H2_3  Hdnum_ge Hdnum_le.
      destruct (Int.ltu ($DNUM) v'8) eqn:Hdnumv'7.
      - apply Intlt_true_is_Zlt in Hdnumv'7.
        destruct H8 as  [[ _ [_ [_ H0]]] |[ [H0| H0] _ ]];tryfalse.
        rewrite Int.unsigned_repr in * by mauto. 
        destruct H5 as [[? ?] | [? [? [? [? ?]]]]];subst;lia.
      - apply Intlt_false_is_Zge in Hdnumv'7.
        destruct H8 as  [[ H0 _ ] |[ _ H0 ]];cbn in H0;tryfalse.
        rewrite Int.unsigned_repr in * by mauto. 
        apply Inteq_false_is_Zneq in H2_3.
        rewrite Int.unsigned_repr in * by mauto. 
        destruct H5 as [[? ?] | [? [? [? [? [? ?]]]]]];subst.
        mauto. 
        apply Inteq_false_is_Zneq in H5.
        rewrite Int.unsigned_repr in * by mauto.
        mauto. } 
    assert (Z.to_nat stepz = compute_step (Z.to_nat (Int.unsigned v'8)) (Z.to_nat DNUM)) as Hstepn.
    { unfold compute_step .
      clear - H8 H5 H4 H2_4 H2_3  Hdnum_ge Hdnum_le.
      destruct (Int.ltu ($DNUM) v'8) eqn:Hdnumi.
      - apply Intlt_true_is_Zlt in Hdnumi.
        destruct H8 as  [[ _ [_ [_ H0]]] |[ [H0| H0] _ ]];tryfalse. 
        rewrite Int.unsigned_repr in * by mauto. 
        destruct H5 as [[? ?] | [? [? [? [? ?]]]]];subst.
        assert (Z.to_nat DNUM <? Z.to_nat (Int.unsigned i) = true)%nat. { apply <- Nat.ltb_lt. lia. }
        rewrite H0. lia.
        assert (Z.to_nat DNUM <? Z.to_nat (Int.unsigned x) = true)%nat. { apply <- Nat.ltb_lt. lia. }
        rewrite H0. lia.
      - apply Intlt_false_is_Zge in Hdnumi.
        destruct H8 as  [[ H0 _ ] |[ _ H0 ]];cbn in H0;tryfalse.
        rewrite Int.unsigned_repr in * by mauto. 
        destruct H5 as [[? ?] | [? [? [? [? [? ?]]]]]];subst.
        assert (Z.to_nat DNUM <? Z.to_nat (Int.unsigned i) = false)%nat. { apply <- Nat.ltb_ge. lia. }
        rewrite H0. lia. 
        assert (Z.to_nat DNUM <? Z.to_nat (Int.unsigned x) = false)%nat. { apply <- Nat.ltb_ge. lia. }
        rewrite H0. lia.  }
    
    hoare forward prim.
    unfold TmrInv, TmrInv', HeapInv', CoreCommuInv, EvtInv.
    hoare normal pre. pure intro.
    rename v'25 into vpthattr.
    rename v'26 into vcspace.
    rename v'27 into v27. 
    rename v'28 into v28. 
    rename v'29 into v29. 
    
    rename v'30 into v'25. 
    rename v'31 into v'26. 
    rename v'32 into v'27. 
    rename v'33 into v'28. 
    rename v'34 into v'29. 
    rename v'35 into v'30. 
    rename v'36 into v'31. 
    rename v'37 into v'32. 
    rename v'38 into v'33. 
    rename v'39 into v'34. 
    rename v'40 into v'35. 
    rename v'41 into v'36. 
    rename v'42 into v'37. 
    rename v'43 into v'38. 
    rename v'44 into v'39. 
    rename v'45 into v'40. 
    rename v'46 into v'41. 
    rename v'47 into v'42. 
    rename v'48 into v'43. 
    rename v'49 into v'44. 
    rename v'50 into v'45. 
    rename v'51 into v'46. 
    rename v'52 into v'47. 
    rename v'53 into v'48. 
    rename v'54 into v'49. 
    rename v'55 into v'50. 
    rename v'56 into v'51. 
    rename v'57 into v'52. 
    rename v'58 into v'53. 
    rename v'59 into v'54. 
    rename v'60 into v'55. 
    rename v'61 into v'56. 
    rename v'62 into v'57. 
    rename v'63 into v'58. 

    hoare name lift ipcrecvid pre.
    hoare name lift ipcsendid pre.
    hoare name lift oscoreheapid pre.
    hoare name lift curcoreid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift absecblsid pre.
    hoare name lift Aop pre.
    (* memcpy (­dstAddr ′, 〈 (Void) ∗ 〉 (IPCMem ′ [′ DNUM] +ₑ step ′ × ′ IPC_STEP), size ′­) *)
    (* rename v'44 into ptrl. rename v'45 into memlls. *)
    rename v'49 into coreheapl.
    rename i1 into size_v.
    rename p into dstAddr_l.
    assert (
    In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v)) \/ 
    ~ In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v))
    ) as HInh by tauto.
    destruct HInh.
    2: {  (*~ In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v))*) 
      (* hoare abscsq. *)
      eapply abscsq_rule'.
      apply noabs_oslinv.
      eapply IPCrecv_high_level_step_memcpy_abt;eauto.
      can_change_aop_solver.
      apply absabort_rule. }
    hoare name lift AOScoreheapl pre.
    (* In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v)) *)
    eapply backward_rule1.
    eapply (ipcrecv_split_coreheapl _ _ _ H18).
    pure intro.
    rename v'21 into cheapl1.
    rename v'49 into cheapl2.
    rename v'60 into vl1.
    rename v'61 into vl2.
    hoare name lift AOSIPCMem pre.
    (* hoare lifts (3::4::6::nil)%nat pre. *)
    eapply backward_rule1.
    eapply (AOSIPCMem_separate _ _ _ (Z.to_nat DNUM) (Z.to_nat stepz)) .
    lia. lia.
    pure intro.
    unfold Memory_Node.
    pure intro.
    (* hoare lifts (1::8::nil)%nat pre. *)
    rename v'59 into vlsrc.
    rewrite <- (firstn_skipn (Z.to_nat (Int.unsigned size_v)) vlsrc).
    assert (
      length(firstn (Z.to_nat (Int.unsigned size_v)) vlsrc) +
      length (skipn (Z.to_nat (Int.unsigned size_v)) vlsrc) =
      Z.to_nat HEAP_MAX_LENGTH)%nat.
    { rewrite <- app_length.
      rewrite firstn_skipn; auto. }
    rewrite <- H40 at 1.
    destruct v'21 as [pb pi].
    eapply seq_rule. 
    eapply call_rule'.
    intuition eauto.
    2:{
      intros.
      unfold getasrt, OS_memcopyPre, OS_memcopyPre'.
      unfold Aarray in *.
      apply Aarray'_app_frame in H41.
      2:{
        rewrite H40.
        rewrite Z2Nat.id;
        unfold HEAP_MAX_LENGTH;
        unfold IPC_STEP; try lia.
        clear; mauto.
      }
      rewrite firstn_length_le in H41.
      2:{
        (* clear - H2 H27. *)
        unfold HEAP_MAX_LENGTH in H38.
        rewrite H38.
        apply Z2Nat.inj_le; mauto.
      }
      unfold Aarray in *.
      sep name lift Aisr Ais aemp_isr_is in H41.
      eapply elim_aemp_isr_is_prop in H41.
      
      sep normal.
      sep eexists.
      trycancel.
      
      sep lifts (7::nil)%nat in H41.
      sep cancel A_isr_is_prop.
      sep cancel Aarray'.
      sep cancel Aarray'.
      sep cancel Aop.

      (* sep name lift aemp_isr_is in H35. *)
      sep split; [exact H41|auto|auto].
    }
    { assert ((Int.unsigned ($ DNUM)) = DNUM).
      { clear - Hdnum_ge Hdnum_le. 
        apply Int.unsigned_repr; mauto. }
      intros. eapply rvl_elim;[symbolic_execution| ].
      eapply rvl_elim.
      eapply symbolic_lemmas.cast_rv_ptr with (t1:= Tptr Tint8); [ | simpl; eauto; tryfalse| intuition (try eexists; auto 1) ..].
      eapply symbolic_lemmas.bop_rv with (t1:= Tptr Tint8);[sep_get_rv | sep_get_rv | simpl; auto | auto | simpl; auto ].
      rewrite H41;rewrite H31;pauto.
      rewrite H41;rewrite H31;cbn.
      rewrite Int.mul_one.
      rewrite Z2Nat.id; try lia.
      auto.
      eapply rvl_elim;[symbolic_execution| apply rvl_nil]. }
    { good_frm_sovler. }
    {
      intros.
      unfold getasrt, OS_memcopyPost, OS_memcopyPost' in H41.
      sep auto.
    }
    {
      intros.
      unfold getasrt, OS_memcopyPre, OS_memcopyPre' in H41.
      sep auto.
    }
    pauto.
    unfold_funpost. hoare normal pre.
    pure intro. inversion H41. inversion H42. 
    subst v'61 v'62 v'63 v'65 v'64.
    fold (ipcrecv_succ_ack (Vint32 i :: Vptr dstAddr_l :: Vint32 size_v :: Vint32 i0 :: v :: nil)) in *.
    repeat (match goal with 
    | H: ?x = ?x |- _ => clear H end).
    hoare lifts (8::15::nil)%nat pre.
    eapply backward_rule1.
    eapply AOScoreheapl_merge;eauto.
    rewrite <- H29. lia.
    rewrite <- H29. lia.
    { assert (vlsrc = (firstn (Z.to_nat (Int.unsigned size_v)) vlsrc) ++ skipn (Z.to_nat (Int.unsigned size_v)) vlsrc).
      { rewrite firstn_skipn;auto. }
      rewrite H42 in H37.
      apply array_type_vallist_match_app in H37. tauto. }
    (* abs step : ipcrecv_memcpy (|Vint32 i :: Vptr dstAddr_l :: Vint32 size_v :: Vint32 i0 :: v :: nil|)*)
    assert (v'53 = v'49).
    { unfold RLH_IpcRecvHeap_P in H13.
    unfold curcore in H13. rewrite H32 in H13.  
    inversion H13. auto. } 
    subst v'53 v'59.
    
    hoare name lift ipcrecvid pre.
    hoare name lift ipcsendid pre.
    hoare name lift oscoreheapid pre.
    hoare name lift curcoreid pre.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift absecblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply IPCrecv_high_level_step_memcpy_succ;eauto.
    {
      instantiate (1:= (cheapl1 ++ (dstAddr_l, (length vl1 + length vl2)%nat, firstn (Z.to_nat (Int.unsigned size_v)) vlsrc ++ vl2) :: cheapl2)).
      unfold update_heapl_addrval. 
      do 5 eexists. splits;auto. }
    can_change_aop_solver.

    (* merge AOSIPCMem *)
    unfold Aarray.
    eapply backward_rule1.
    { remember (firstn (Z.to_nat (Int.unsigned size_v)) vlsrc) as vlsrc1.
      remember (skipn (Z.to_nat (Int.unsigned size_v)) vlsrc) as vlsrc2.
      intros.
      rewrite <- H43 in H42.
      sep lifts (16::18::nil)%nat in H42. 
      erewrite  <- Aarray'_app_frame in H42.
      subst vlsrc1 vlsrc2. exact H42.
      rewrite H40. 
      erewrite Z2Nat.id;apply HEAP_MAX_LENGTH_range. }
    rewrite H40. erewrite firstn_skipn.
    eapply backward_rule1.
    eapply fold_Memory_Node;eauto.
    rewrite Int.unsigned_repr.
    2: clear - Hstepz_ge Hstepz_lt; rewrite Z2Nat.id; mauto.
    hoare lifts (1::18::19::20::nil)%nat pre.
    rewrite! Z2Nat.id.
    eapply backward_rule1.
    eapply ipcsend_AOSIPCMem_merge; eauto.
    lia. lia. 2: lia.
    (* EXIT_CRITICAL;ₛ *)
    eapply seq_rule.
      (* hoare forward. *)
    {
      hoare lifts (2::nil)%nat pre.
      eapply excrit1_rule'_ISnil_ISRemp'''_lg.
      intros.
      {
        unfold OldOSInvWL.
        sep pauto.
        sep cancel tcbdllflag.
        sep cancel p_local.
        unfold EvtInv, TmrInv, TmrInv', HeapInv', CoreCommuInv.
        sep normal.
        sep eexists.
        sep name lift Aisr Ais Aier in H42.
        eapply add_aemp_isr_is_prop in H42.
        sep autocancel.
        sep split.
        exact H42.
        all: try auto.
        rewrite list_append_map in *.
        rewrite list_append_map in *.
        cbn [map fst] in *. auto.
      }
      good_frm_sovler.
    }
    
    (* If (flag ′ !=ₑ ′ IPC_NONACK) *)
    assert (Int.unsigned i0  <= IPC_BROAD)%Z as Hflag.
    { clear -H2_4 .
      simpl_intltbool.
      lia. }
    rename i0 into flag_v.
    hoare forward;pauto.
    2:{ (* RETURN ′ OS_NO_ERR *)
        instantiate (1:= EX return_v,
        <|| END Some return_v ||>  **
        [| Int.eq flag_v ($ IPC_BROAD) = false /\ return_v  = (V$ OS_NO_ERR) \/ 
        Int.eq flag_v ($ IPC_BROAD) = true /\ return_v  = (Vint32 v'8)  |] ** 
        LV ipcinfo @ Int32u |-> (nth_val' (Z.to_nat DNUM) IPCInfoList) **
        Aisr empisr **
        Aie true **
        Ais nil **
        Acs nil **
        EX ier, Aier ier **
        p_local OSLInv tid init_lg **
        LV srcCore @ char_t |-> Vint32 v'8 **
        LV IPCBroad_cur @ long |-> v'7 **
        LV tmpsem @ OS_EVENT ∗ |-> v'6 **
        LV flag @ char_t |-> Vint32 flag_v **
        LV size @ long |-> Vint32 size_v **
        LV dstAddr @ (char_t) ∗ |-> Vptr dstAddr_l **
        LV step @ Int32u |-> (V$ stepz) **
        A_dom_lenv
        ((flag, Int8u)
         :: (size, Int32u)
            :: (dstAddr, (Int8u) ∗)
               :: (srcCore, Int8u)
                  :: (IPCBroad_cur, Int32u)
                     :: (tmpsem, OS_EVENT ∗)
                        :: (step, Int32u) :: (ipcinfo, Int32u) :: nil)).
        hoare forward.
        (*Branch : true  flag != nonack*)  
        (* If (flag ′ -=ₑ ′ IPC_BROAD){RETURN srcCore ′};ₛ *)
        hoare forward.
        pauto.
        pauto.
        (* pauto. *)
        pure intro.
        assert (Int.eq flag_v ($ IPC_BROAD) = true) by pauto.
        destruct H42 as [[? ?] | [? ?]];[ tryfalse | subst v'53].
        (* RETURN srcCore ′ *)
        hoare forward.
        hoare forward.
        pure intro.
        assert (Int.eq flag_v ($ IPC_BROAD) = false).
        { clear -H45. 
          destruct (Int.eq flag_v ($ IPC_BROAD));auto.
         simpl in H45. destruct H45;tryfalse. }
        destruct H42 as [[? ?] | [? ?]];[ subst v'53 | tryfalse].
        (* RETURN ′ OS_NO_ERR *)
        hoare forward.
        (*Branch : false  flag is nonack*)  
        pure intro.
        assert (Int.eq flag_v ($ IPC_NONACK) = true).
        { clear - H42. destruct (Int.eq flag_v ($ IPC_NONACK));auto.
        simpl in H42. unfold Int.notbool in *.
        assert (Int.eq Int.zero Int.zero = true) by pauto.
        rewrite H in *. destruct H42; tryfalse. } 
        hoare abscsq.
        apply noabs_oslinv.
        eapply IPCrecv_high_level_step_nonack;eauto.
        can_change_aop_solver.
        (* If (flag ′ ==ₑ ′ IPC_BROAD) *)
        hoare forward.
        pauto.
        pauto.
        instantiate (1:= Afalse).
        pure intro.
        assert (Int.eq flag_v ($ IPC_BROAD) = true) by pauto.
        destruct H6 as [[H6 ?] | [H6 ? ]];[ tryfalse| ].
        exfalso.
        clear - H6 H41.
        rewrite Int_eq_dec in *.
        subst.
        unfold IPC_BROAD, IPC_NONACK in *.
        mauto.
        hoare forward.
        pure intro.
        assert (Int.eq flag_v ($ IPC_BROAD) = false).
        { clear -H44. destruct (Int.eq flag_v ($ IPC_BROAD));auto.
         simpl in H44. destruct H44;tryfalse. }
        destruct H6 as [[H6 ?] | [H6 ? ]];[ subst v'5|  tryfalse ].
        (* RETURN ′ OS_NO_ERR *)
        hoare forward.
      }
    (*Branch : true flag != nonack*)
    pure intro.
    hoare abscsq.
    apply noabs_oslinv.
    apply IPCrecv_high_level_step_ack.
    can_change_aop_solver.
    (* ipcinfo ′ =ₑ ′ 0;ₛ *)
    hoare forward.
    (* IF (′ DNUM ==ₑ ′ 0) *)
    hoare forward;pauto. 
    { (* Branch: dnum = 0 *) hoare forward. }
    { (*Branch: else dnum != 0 *) 
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 1) *)
      hoare forward;pauto.
      { (*Branch : dnum = 1*) hoare forward. }
    { (*Branch :  dnum != 0, 1*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 2) *)
      hoare forward;pauto.
      { (*Branch : dnum = 2*) hoare forward. }
    { (*Branch :  dnum != 0, 1, 2*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 3) *)
      hoare forward;pauto.
      { (*Branch : dnum = 3*) hoare forward. }
    { (*Branch :  dnum != 0, 1, 2, 3*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 4) *)
      hoare forward;pauto.
      { (*Branch : dnum = 4*) hoare forward. }
    { (*Branch :  dnum != 0, 1, 2, 3, 4*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 5) *)
      hoare forward;pauto.
      { (*Branch : dnum = 5*) hoare forward. }
    { (*Branch :  dnum != 0, 1, 2, 3, 4, 5*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 6) *)
      hoare forward;pauto.
      { (*Branch : dnum = 6*) hoare forward. }
    { (*Branch :  dnum != 0, 1, 2, 3, 4, 5, 6*)
      pure intro.
      case_ipcinfo_false_asrt.
      (* IF (′ DNUM ==ₑ ′ 7) *)
      hoare forward;pauto.
      { (*Branch : dnum = 7*) hoare forward. }
      { (*Branch :  dnum != 0, 1, 2, 3, 4, 5, 6, 7*)
        instantiate (1:= Afalse).
        pure intro.
        case_ipcinfo_false_asrt.
        pose proof DNUM_destruct.
        destruct H41 as [Hd | [Hd | [Hd | [Hd |[Hd | [Hd | [Hd | Hd]]]]]]];
        rewrite Hd in *;rewrite Int.eq_true in *;tryfalse. }
    } } } } } } }
    assert (Int.eq flag_v ($ IPC_BROAD) = false /\ v'5 = V$ OS_NO_ERR \/
    Int.eq flag_v ($ IPC_BROAD) = true /\ v'5 = Vint32 v'8).
    { clear -H5 H6.
      destruct H6 as [? | [? ?]]; [ auto | ].
      subst v'5.
      destruct H5 as [ [? ?] | [? [? [? [? ?]]]]];[tryfalse | subst;auto ]. }
    (* GENERATEIPC (srcCore ′, ipcinfo ′ |ₑ ′ IPC_MESSAGE_ACK) *)
    eapply disj_rule.
    {
      (*Branch : dnum = 0*)
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 0%nat)%nat as Hdnumeq;
      [ clear - H52 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H52;
      repeat progress (rewrite Int.unsigned_repr in H52 by mauto);lia | ].
      assert ((V$ CORE0_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac]; rewrite H53.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H53, H54.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 1%nat)%nat as Hdnumeq;
      [ clear - H53 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H53;
      repeat progress (rewrite Int.unsigned_repr in H53 by mauto);lia | ].
      assert ((V$ CORE1_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H54.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H54, H55.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 2%nat)%nat as Hdnumeq;
      [ clear - H54 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H54;
      repeat progress (rewrite Int.unsigned_repr in H54 by mauto);lia | ].
      assert ((V$ CORE2_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H55.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H55, H56.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 3%nat)%nat as Hdnumeq;
      [ clear - H55 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H55;
      repeat progress (rewrite Int.unsigned_repr in H55 by mauto);lia | ].
      assert ((V$ CORE3_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H56.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H56, H57.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 4%nat)%nat as Hdnumeq;
      [ clear - H56 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H56;
      repeat progress (rewrite Int.unsigned_repr in H56 by mauto);lia | ].
      assert ((V$ CORE4_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H57.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H57, H58.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 5%nat)%nat as Hdnumeq;
      [ clear - H57 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H57;
      repeat progress (rewrite Int.unsigned_repr in H57 by mauto);lia | ].
      assert ((V$ CORE5_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H58.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H58, H59.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 6%nat)%nat as Hdnumeq;
      [ clear - H58 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H58;
      repeat progress (rewrite Int.unsigned_repr in H58 by mauto);lia | ].
      assert ((V$ CORE6_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H59.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H59, H60.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    pure intro.
    eapply disj_rule.
    {
      hoare normal pre;
      repeat (apply ex_intro_rule; intros);
      pure intro.
      let Hinteq := fresh "H" in let Hdnumeq := fresh "H" in
      case_ipcinfo_true_asrt Hinteq.
      assert (Z.to_nat DNUM = 7%nat)%nat as Hdnumeq;
      [ clear - H59 Hdnum_ge Hdnum_le; apply Inteq_true_is_Zeq in H59;
      repeat progress (rewrite Int.unsigned_repr in H59 by mauto);lia | ].
      assert ((V$ CORE7_IPC) = nth_val' (Z.to_nat DNUM) IPCInfoList);
      [rewrite Hdnumeq;unfold IPCInfoList;auto|idtac].  rewrite H60.
      hoare abscsq;[apply noabs_oslinv 
      | eapply IPCrecv_high_level_step_choose_ipcinfo;[eauto | eauto |can_change_aop_solver ]| ].
      unfold IPCINFO_case; rewrite Nat.eqb_refl.
      eapply forward_rule2.
      {
        eapply generateipc_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id in *.
        1,2: apply Int.unsigned_range_2.
        2: unfold p_local, CurLINV; sep auto.
        intros.
        apply aconj_intro.
        rewrite Z2Nat.id.
        rewrite Int.repr_unsigned.
        symbolic_execution.
        apply Int.unsigned_range_2.
        unfold IPCInfoList in *.
        rewrite Hdnumeq in H60, H61.
        symbolic_execution.
      }
      sep pauto.
      sep autocancel. auto.
    }
    (*Branch :  dnum != 0, 1, 2, 3, 4, 5, 6, 7*)
    pure intro.
    case_ipcinfo_false_asrt.
    pose proof DNUM_destruct.
    destruct H46 as [Hd | [Hd | [Hd | [Hd |[Hd | [Hd | [Hd | Hd]]]]]]];
    rewrite Hd in *;rewrite Int.eq_true in *;tryfalse.
Qed.
