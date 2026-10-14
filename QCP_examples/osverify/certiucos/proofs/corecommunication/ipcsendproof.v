Require Import ucos_include.
Require Import Lia.

(* Require Import tmr_aux. *)

Require Import sem_lab.
Require Import ternary_assignment.

Require Import aux_pureLib.
Require Import corecommu_rules.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.
Require Import abs_op_corecommu_rules.
Require Import corecommu_SemPtr_assign_rules.
Require Import evaux_pure.
(* Require Import symbolic_lemmas. *)


Set Nested Proofs Allowed.

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

Lemma ipcsend_error_absinfer:
    forall (P : asrt) (flag_v size_v dstCore_v : int32) (srcAddr_v : val) (sch : ossched),
      (srcAddr_v = Vnull \/
      Int.ltu size_v ($ 1) = true \/
      Int.ltu ($ IPC_STEP) size_v = true \/
      Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v = true \/
      Int.eq dstCore_v ($ DNUM) = true \/
      Int.ltu ($ IPC_BROAD) flag_v = true) ->
      can_change_aop P ->
      (Int.unsigned flag_v <= 255)%Z ->
      (Int.unsigned dstCore_v <= 255)%Z ->
      isptr srcAddr_v ->
      sch ⊢  <|| ipcsend_err_invalid
      (|Vint32 dstCore_v :: srcAddr_v :: Vint32 size_v :: Vint32 flag_v :: nil|) ||>  ** P ⇒  <|| END Some (V$ EINVAL) ||>  ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma ipcsend_absinfer_before_pend_succ:
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

Lemma ipcsend_absinfer_after_pend_succ:
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

(* wrapper for split_coreheapl *)
Lemma ipcsend_split_coreheapl:
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
  [| array_type_vallist_match Tint8 vl1 /\ (length (vl1 ++ vl2) <= (Z.to_nat HEAP_MAX_LENGTH ))%nat|] ** P.
Proof.
  intros.
  eapply In_heapl_addrval_split in H0; [ | apply H].
  sep destruct H0.
  sep split in H0.
  destruct H1; subst coreheapl.
  eapply split_coreheapl with (m:=m) in H0; auto.
  sep auto.
Qed.

Lemma ipcsend_AOSIPCMem_split:
  forall pl memlls P dstCore_v step,
    Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v = false ->
    (step < 7)%nat -> 
    AOSIPCMem pl memlls ** P ==>
    EX p memls meml, Memory_Node step p meml ** Memory_sigcore_aux_rm step O p memls **
    AOSIPCMem_aux_rm (Z.to_nat (Int.unsigned dstCore_v)) pl memlls **  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl 
    **  [| isvptr_list pl /\ length pl = 8%nat /\ length memlls = 8%nat|] **
    [| nth_val' (Z.to_nat (Int.unsigned dstCore_v)) pl = Vptr p /\  nth_error memlls (Z.to_nat (Int.unsigned dstCore_v)) = Some memls /\ length memls = 7%nat /\ 
      nth_error memls step = Some meml|] ** P.
Proof.
  (* intros ? ? ? ? ? ?. *)
  intros.
  apply AOSIPCMem_separate; auto.
  apply Intlt_false_is_Zge in H.
  apply nat_8_range_conver.
  assert ($ CORENUM -ᵢ $ 1 = $ 7); auto.
  rewrite H2 in H.
  rewrite int_usign_eq in H; pauto; try lia.
  mauto.
Qed.

Lemma ipcsend_absimp_generateipc_broad_choice:
  forall sch dst x P,
  can_change_aop P ->
  x = 0%nat \/
  x = 1%nat \/
  x = 2%nat \/
  x = 3%nat \/ x = 4%nat \/ x = 5%nat \/ x = 6%nat \/ x = 7%nat ->
  absinfer sch
    (<|| ipcsend_generateipc_broad (Vint32 dst) ||> ** P)
    (<|| coreint (Z.to_nat (Int.unsigned dst)) (Vint32 (IPCINFO_brach x IPC_MESSAGE_BROAD))||> ** P).
Proof.
  intros.
  unfold ipcsend_generateipc_broad.
  destruct H0 as [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]; subst.
  - my_infer_branch 0%nat.
  - my_infer_branch 1%nat.
  - my_infer_branch 2%nat.
  - my_infer_branch 3%nat.
  - my_infer_branch 4%nat.
  - my_infer_branch 5%nat.
  - my_infer_branch 6%nat.
  - my_infer_branch 7%nat.
Qed.

Lemma IPCSendProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api IPCsend ipcsendapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api IPCsend ipcsendapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api IPCsend = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{p }} s {{ Afalse }}.
Proof.
  init_spec.
  (* hoare unfold. *)

  rename i into dstCore_v.
  rename x1 into srcAddr_v.
  rename i1 into size_v.
  rename i0 into flag_v.
  rename v'2 into ipcinfo_v.
  rename v'1 into step_v.
  rename v'0 into err_v.
  (* v' is not used any where *)

  (* If (srcAddr ′ ==ₑ NULL ||ₑ  size′ <ₑ ′1 ||ₑ size′ >ₑ ′IPC_STEP ||ₑ 
        dstCore′ >ₑ( ′CORENUM − ′1) ||ₑ dstCore′ ==ₑ ′DNUM ||ₑ 
        flag′ >ₑ ′IPC_BROAD) *)
  hoare forward; pauto.
  (* side conditions for the first if statement *)
  {
    destruct (Int.ltu size_v ($ 1));
    destruct H3 as [? | [? ?]]; subst; auto;
    unfold val_inj; destruct x; auto.
  }
  {
    destruct (Int.ltu size_v ($ 1));
    destruct (Int.ltu ($ IPC_STEP) size_v);
    destruct H3 as [? | [? ?]]; subst; auto;
    destruct x; auto.
  }
  {
    destruct (Int.ltu size_v ($ 1));
    destruct (Int.ltu ($ IPC_STEP) size_v);
    destruct (Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v);
    destruct H3 as [? | [? ?]]; subst; auto;
    destruct x; auto.
  }
  {
    destruct (Int.ltu size_v ($ 1));
    destruct (Int.ltu ($ IPC_STEP) size_v);
    destruct (Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v);
    destruct (Int.eq dstCore_v ($ os_code_defs.DNUM));
    destruct H3 as [? | [? ?]]; subst; auto;
    destruct x; auto.
  }
  {
    destruct (Int.ltu size_v ($ 1));
    destruct (Int.ltu ($ IPC_STEP) size_v);
    destruct (Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v);
    destruct (Int.eq dstCore_v ($ os_code_defs.DNUM));
    destruct (Int.ltu ($ IPC_BROAD) flag_v);
    destruct (Int.eq flag_v ($ IPC_BROAD));
    destruct H3 as [? | [? ?]]; subst; auto;
    destruct x; auto.
  }

  (* RETURN ′EINVAL *)
  {
    hoare unfold.
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      eapply absinfer_choice1;
      [can_change_aop_solver | |
      intros ? Hs; apply Hs ].
      can_change_aop_solver.
    }
    hoare abscsq; [apply noabs_oslinv | | ].
    {
      assert (srcAddr_v = Vnull \/ 
      Int.ltu size_v ($ 1) = true \/
      Int.ltu ($ IPC_STEP) size_v = true \/
      Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v = true \/
      Int.eq dstCore_v ($ DNUM) = true \/
      Int.ltu ($ IPC_BROAD) flag_v = true ).
      {
        destruct H3 as [H3 | H3] ;[ | destruct H3 as [x H3];destruct x]; subst srcAddr_v;
        destruct (Int.ltu size_v ($ 1));
        destruct (Int.ltu ($ IPC_STEP) size_v);
        destruct (Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v);
        destruct (Int.eq dstCore_v ($ DNUM));
        destruct (Int.ltu ($ IPC_BROAD) flag_v);
        destruct (Int.eq flag_v ($ IPC_BROAD)); try tauto.
      }
      eapply ipcsend_error_absinfer; auto.
      can_change_aop_solver.
    }
    hoare forward; auto.
  }

  hoare forward.
  pure intro.

  (* reshape *)
  assert ( ((exists p, srcAddr_v = Vptr p) /\ Int.ltu size_v ($ 1) = false /\ Int.ltu ($ IPC_STEP) size_v = false /\ Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v = false /\ Int.eq dstCore_v ($ os_code_defs.DNUM)  = false /\ Int.ltu ($ IPC_BROAD) flag_v = false )).
  {
    destruct H3 as [H3 | H3];[ | destruct H3 as [x H3];destruct x]; subst srcAddr_v;
    destruct (Int.ltu size_v ($ 1)); 
    destruct (Int.ltu ($ IPC_STEP) size_v);
    destruct (Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v);
    destruct (Int.eq dstCore_v ($ os_code_defs.DNUM));
    destruct (Int.ltu ($ IPC_BROAD) flag_v); 
    assert (Int.ltu Int.zero Int.one = true) by pauto. 
    repeat progress (cbn in * || rewrite H3 in *).
    all : try (destruct H;tryfalse).
    splits;eauto.
  }
  clear H.
  
  (* select second branch of spec code *)
  hoare abscsq; [apply noabs_oslinv | | ].
  {
    eapply absinfer_choice2;
    [can_change_aop_solver | |
    intros ? Hs; apply Hs ].
    can_change_aop_solver.
  }

  (* GETSEM dstCore′;ₛ *)
  hoare forward prim.
  {
    eapply getsem_rule.
    can_change_aop_solver.
    {
      assert (0 <= Int.unsigned dstCore_v)%Z by mauto.
      apply Z2Nat.id in H.
      rewrite H; clear H.
      apply Int.unsigned_range_2.
    }
    {
      sep pauto.
      assert (0 <= Int.unsigned dstCore_v)%Z by mauto.
      apply Z2Nat.id in H9.
      rewrite H9; clear H9.
      rewrite Int.repr_unsigned.
      symbolic execution.
      pauto.
    }
    {
      intros.
      unfold CurLINV.
      unfold p_local in H.
      sep auto.
    }
  }

  pure intro.
  pose proof dnum_range as Hdnum_range.
  pose proof H0 as H0'.
  pose proof H2 as H2'.
  pose proof H5 as H5'.
  pose proof H6 as H6'.
  pose proof H7 as H7'.
  eapply Intlt_false_is_Zge in H0, H2, H5, H7.
  eapply Inteq_false_is_Zneq in H6.
  assert (Int.sub ($ CORENUM) ($ 1) = $ (CORENUM - 1)) as Hcorenum_sub1.
  {
    unfold Int.sub.
    unfold CORENUM.
    clear. mauto.
  }
  rewrite Hcorenum_sub1 in H5.
  rewrite Int.unsigned_repr in H0, H2, H5, H6, H7.
  2,3,4,5,6:
    unfold IPC_BROAD, CORENUM, IPC_STEP;
    clear - Hdnum_range; mauto.

  (* IF (′ DNUM >ₑ dstCore ′){step ′ =ₑ ′ DNUM − ′ 1}ELSE {
step ′ =ₑ ′ DNUM};ₛ *)
  eapply seq_rule; [wzy_resolve_ternary_assign| ].

  pure intro.
  rename v'0 into stepz.
  assert (
    (((Int.unsigned dstCore_v) > DNUM /\
    stepz = DNUM ) \/
    ((Int.unsigned dstCore_v) < DNUM /\
    stepz = DNUM - 1))
    /\ 0 <= stepz < CORENUM - 1
  )%Z as [Hstepz [Hstepz_r1 Hstepz_r2]].
  {
    clear - H6 H H8 H9 H5.
    assert (
      ((Int.unsigned dstCore_v > DNUM)%Z /\ stepz = DNUM /\
      (0 <= stepz < CORENUM - 1) \/
      (Int.unsigned dstCore_v < DNUM)%Z /\ stepz = (DNUM - 1) /\
      (0 <= stepz < CORENUM - 1))%Z
    ); try tauto.
    {
      destruct H; [right|left].
      - destruct (Int.ltu dstCore_v ($ DNUM)) eqn:eq;
        simpl in H; destruct H; tryfalse.
        eapply Intlt_true_is_Zlt in eq.
        rewrite Int.unsigned_repr in eq; [ |mauto].
        split; try lia.
        destruct H0 as [_ [_ ?]].
        rewrite Int.unsigned_repr in H0;[ |mauto].
        rewrite Int.unsigned_repr in H0;[ |mauto].
        split; auto.
        pose proof Int.unsigned_range_2 dstCore_v.
        unfold CORENUM; lia.
      - destruct (Int.ltu dstCore_v ($ DNUM)) eqn:eq;
        simpl in H; destruct H;
        [destruct H; inversion H| ].
        eapply Intlt_false_is_Zge in eq.
        rewrite Int.unsigned_repr in eq;[ |mauto].
        split; try lia.
    }
  }
  clear H.
  
  (* both branch together *)
  {
    (* ENTER_CRITICAL;ₛ *)
    hoare forward prim.

    unfold TmrInv, TmrInv', HeapInv'.

    hoare normal pre.
    pure intro.

    rename v'16 into vpthattr.
    rename v'17 into vcspace.
    rename v'18 into v18. 
    rename v'19 into v19. 
    rename v'20 into v20. 
    rename v'21 into v'16. 
    rename v'22 into v'17. 
    rename v'23 into v'18. 
    rename v'24 into v'19. 
    rename v'25 into v'20. 
    rename v'26 into v'21. 
    rename v'27 into v'22. 
    rename v'28 into v'23. 
  

    rename x into srcAddr_v.

    rename v'21 into coreheapl.
    rename v'22 into coreheape.

    (*list (addrval * nat * list val)*)

    assert (
      ~ In_heapl_addrval coreheapl srcAddr_v (Z.to_nat (Int.unsigned size_v)) \/
      In_heapl_addrval coreheapl srcAddr_v (Z.to_nat (Int.unsigned size_v))
    ) as Hin_heapl by tauto.
    destruct Hin_heapl.

    (*  ~ In_heapl_addrval coreheapl srcAddr_v (Z.to_nat (Int.unsigned size_v)) *)
    {
      hoare abscsq; [apply noabs_oslinv| | ].
      eapply absinfer_conseq_pre.
      2:{
        intros.
        exact H15.
      }
      {
        eapply absinfer_trans;
        [eapply absinfer_seq;[
          can_change_aop_solver|
          | eapply ipcsend_absimp_memcpy_fail; auto
        ]| ].
        1,2:can_change_aop_solver.
        eapply absinfer_seq_abt;
        [ | |intros s Hs; exact Hs ];
        can_change_aop_solver.
      }
      apply absabort_rule.
    }

    (* branch: In_heapl_addrval coreheapl srcAddr_v (Z.to_nat (Int.unsigned size_v)) *)
    {
      hoare lifts (2::nil)%nat pre.
      eapply backward_rule1;
      [apply (In_heapl_addrval_split _ _ _ H14) | ].
      pure intro.
      rename v'21 into cheapl1.
      rename v'22 into cheapl2.
      rename v'24 into n.
      rename v'25 into vl1.
      rename v'26 into vl2.
      eapply backward_rule1;
      [apply (AOScoreheapl_length_frm _ _ _ _ _ (in_elt _ _ _)) | ].
      rewrite app_length.
      pure intro.

      eapply backward_rule1;
      [eapply (Get_heapl_addrval_in_list _ _ _ _ _ _ (in_elt _ _ _)) | ].

      unfold CoreCommuInv.
      hoare normal pre.
      pure intro.

      rename v'21 into sendh.
      rename v'27 into memll.
      rename H15 into Hsendh.

      hoare lift 9%nat pre.
      assert (
        forall P,
        AOSIPCMem v'26 memll ** P ==>
        [|length memll = Z.to_nat CORENUM|] **
        AOSIPCMem v'26 memll ** P
      ) as Htmp.
      {
        clear.
        unfold AOSIPCMem.
        intros. unfold CORENUM.
        sep auto. try lia.
      }
      eapply backward_rule1;
      [eapply Htmp | ].
      clear Htmp; pure intro.

      (* reshape precondition to split dst/src arrays *)
      (* hoare lifts (17::nil)%nat pre. *)
      eapply backward_rule1;
      [apply (ipcsend_AOSIPCMem_split _ _ _ dstCore_v (Z.to_nat stepz)); auto | ].
      (* { pose proof dnum_range; lia. } *)
      {
        unfold CORENUM in Hstepz_r2.
        apply symbolic_lemmas.ge0_z_nat_le; lia.
      }
      pure intro.
      unfold Memory_Node. 
      
      (* destruct (type_eq v'29 dyn_refac_cfg) eqn : typeeq.
      2: { *)
      pure intro. clear H31.

      (* rename v' into meml. *)
      rename v'29 into vldst.

      remember (Z.to_nat (Int.unsigned dstCore_v) -
      (if (Z.to_nat DNUM <? Z.to_nat (Int.unsigned dstCore_v))%nat
      then 1%nat else 0%nat))%nat as sendh_idx.
      assert (
        (Int.unsigned dstCore_v > DNUM)%Z /\
         stepz = DNUM /\
         sendh_idx = (Z.to_nat (Int.unsigned dstCore_v) - 1)%nat
        \/
         (Int.unsigned dstCore_v < DNUM)%Z /\
         stepz = (DNUM - 1)%Z /\
         sendh_idx = Z.to_nat (Int.unsigned dstCore_v)
      ) as Hsendh_idx.
      {
        clear - Heqsendh_idx Hstepz.
        destruct (Z.to_nat DNUM <? Z.to_nat (Int.unsigned dstCore_v))%nat eqn:eq.
        - apply Nat.ltb_lt in eq.
          apply Z2Nat.inj_lt in eq;
          [ | pose proof dnum_range; lia |
          pose proof Int.unsigned_range_2 dstCore_v; mauto ].
          left; destruct Hstepz as [?|[? ?]]; try tauto; try lia.
        - apply Nat.ltb_ge in eq.
          apply Z2Nat.inj_le in eq;
          [ | pose proof Int.unsigned_range_2 dstCore_v; mauto | pose proof dnum_range; lia].
          right; destruct Hstepz as [[? ?]|?]; try tauto; try lia.
      }

      assert (exists sh', set_sendheap sendh_idx sendh (Z.to_nat (Int.unsigned size_v)) vl1 sh') as [sendh' ?].
      {
        apply set_sendheap_valid with (memll:=memll); auto.
        unfold CORENUM; simpl; lia.
      }

      (* forward spec code *)
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply absinfer_seq.
        can_change_aop_solver.
        2:{
          eapply absinfer_conseq_pre.
          2:{
            intros.
            sep lifts (1::7::21::nil)%nat in H32.
            apply H32.
          }
          eapply ipcsend_absimp_memcpy_succ with (step_v:=sendh_idx) (vl:=vl1) (sendh':=sendh'); auto.
          can_change_aop_solver.
          rewrite <- H16; apply H21.
        }
        can_change_aop_solver.
      }

      rewrite <- (firstn_skipn (Z.to_nat (Int.unsigned size_v)) vldst).

      assert (
        length(firstn (Z.to_nat (Int.unsigned size_v)) vldst) +
        length (skipn (Z.to_nat (Int.unsigned size_v)) vldst) =
        Z.to_nat HEAP_MAX_LENGTH
      )%nat as Hvldst_len.
      {
        rewrite <- app_length.
        rewrite firstn_skipn; auto.
      }
      rewrite <- Hvldst_len at 1.

      hoare lifts (21::nil)%nat pre.
      eapply backward_rule1;
      [apply split_coreheapl with (m:=(Z.to_nat (Int.unsigned size_v))); auto | ].
      pure intro.

      eapply seq_rule.
      {
        eapply call_rule'.
        intuition eauto.
        4:{
          intros.
          unfold getasrt, OS_memcopyPost, OS_memcopyPost' in H35.
          exists init_lg.
          sep auto.
        }
        4:{
          intros.
          unfold getasrt, OS_memcopyPre, OS_memcopyPre' in H35.
          exists init_lg.
          sep auto.
        }
        2:{
          intros.
          unfold getasrt, OS_memcopyPre, OS_memcopyPre'.
          sep lifts (6::nil)%nat in H35.
          apply Aarray'_app_frame in H35.
          2:{
            rewrite Hvldst_len.
            rewrite Z2Nat.id;
            unfold HEAP_MAX_LENGTH;
            unfold IPC_STEP; try lia.
            clear; mauto.
          }
          rewrite firstn_length_le in H35.
          2:{
            unfold HEAP_MAX_LENGTH in H30.
            rewrite H30.
            apply Z2Nat.inj_le; mauto.
          }
          unfold Aarray.
          unfold Aarray in H35.
          sep name lift Aisr Ais aemp_isr_is in H35.
          eapply elim_aemp_isr_is_prop in H35.
          
          sep normal.
          sep eexists.
          trycancel.
          sep lifts (5::42::1::4::nil)%nat in H35.
          sep autocancel.
          sep split; [exact H35|auto|auto].
        }
        all: auto.
        intros.
        apply rvl_elim.
        2:{
          apply rvl_elim.
          sep get rv.
          apply rvl_elim.
          sep get rv.
          apply rvl_nil.
        }
        sep get rv.
        {
          destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
          clear -eq H4.
          apply leb_bytemax_true_intro in H4.
          lia.
        }
        {
          rewrite H23; auto.
        }
        {
          rewrite H23.
          destruct v'21.
          unfold get_off_addr.
          simpl.
          rewrite Int.mul_one.
          rewrite Z2Nat.id; try lia.
          auto.
        }
        good_frm_sovler.
      }

      (* reshape precondition: destruct postcondition of call *)
      unfold_funpost.
      hoare normal pre.
      pure intro.
      assert (
        (firstn (Z.to_nat (Int.unsigned size_v)) vldst) = v'33 /\
        vl1 = v'34 /\
        (END None;;
                  (ipcsend_generateipc_broad (Vint32 dstCore_v)
                   ?? ipcsend_generateipc_rdy (Vint32 dstCore_v));;
                  (ipcsend_before_pend (Vint32 dstCore_v);;
                   spec_code_cons
                     (ipcsend_sendsempend (Vint32 dstCore_v) (V$ OS_NO_ERR))
                     (ipcsend_after_pend (|nil|);;
                      ipcsend_postsem (Vint32 dstCore_v);;
                      END Some (V$ OS_NO_ERR))
                   ?? END None;;
                      ipcsend_postsem (Vint32 dstCore_v);;
                      END Some (V$ OS_NO_ERR))) = v'35
      ) as [? [? ?]];
      [inversion H36; tauto |
      subst v'33 v'34 v'35; clear H36 ].
      inversion H35; subst v'30 v'31 v'32; clear H35.
      destruct v'21.
      
      (* merge coreheap *)
      hoare lifts (9::13::nil)%nat pre.
      eapply backward_rule1;
      [apply AOScoreheapl_merge; auto; try lia | ].
      { rewrite <- app_length; lia. }
      
      (* merge IPCMem *)
      hoare lifts (9::12::nil)%nat pre.
      unfold Aarray at 1.
      unfold get_off_addr at 2; simpl fst; simpl snd.
      rewrite Z2Nat.id; try lia.
      rewrite <- H37 at 1 2.

      assert ( (length vl1 + length (skipn (Z.to_nat (Int.unsigned size_v)) vldst))%nat = (length vldst)).
      {
        rewrite H37.
        rewrite skipn_length.
        rewrite Nat.add_comm.
        apply Nat.sub_add.
        rewrite H30.
        rewrite app_length in H34; lia.
      }

      eapply backward_rule1;
      [apply Aarray'_app_frame; try lia | ].
      {
        rewrite H35, H30.
        unfold HEAP_MAX_LENGTH, IPC_STEP.
        replace (Z.of_nat (Z.to_nat 10240)) with (10240)%Z; [ |lia].
        clear; mauto.
      }
      rewrite H35.
      pose proof nth_error_split _ _ H26 as [meml1 [meml2 [? ?]]].
      pose proof nth_error_split _ _ H24 as [memll1 [memll2 [? ?]]].
      subst.

      rewrite H30.
      eapply backward_rule1;
      [apply fold_Memory_Node; auto| ].
      {
        rewrite array_type_vallist_match_app; split; auto.
        rewrite <- firstn_skipn with (n:=(Z.to_nat (Int.unsigned size_v))) in H29.
        apply array_type_vallist_match_app in H29; tauto.
      }
      {
        rewrite app_length; lia.
      }

      hoare lift 14%nat pre.
      eapply backward_rule1;
      [apply ipcsend_Memory_sigcore_aux_updatei with (meml':=(vl1 ++ skipn (Z.to_nat (Int.unsigned size_v)) vldst)); auto | ].
      hoare lift 15%nat pre.
      eapply backward_rule1;
      [apply ipcsend_AOSIPCMem_aux_updatei with (memls':=(meml1 ++ (vl1 ++ skipn (Z.to_nat (Int.unsigned size_v)) vldst) :: meml2)); auto; try lia | ].
      
      rewrite Int.unsigned_repr.
      2:{
        clear - Hstepz_r1 Hstepz_r2.
        unfold CORENUM in Hstepz_r2.
        mauto.
      }

      hoare lifts (3::2::1::16::nil)%nat pre.
      eapply backward_rule1;
      [eapply ipcsend_AOSIPCMem_merge; auto; try lia | ].
      {
        rewrite app_length in *; auto.
      }
      {
        rewrite nth_error_app2; try lia.
        rewrite H40. rewrite Nat.sub_diag.
        auto.
      }
      {
        rewrite app_length in *; auto.
      }
      {
        rewrite nth_error_app2; try lia.
        rewrite H38. rewrite Nat.sub_diag.
        auto.
      }

      assert(
        RLH_IpcSendHeap_P (memll1 ++ (meml1 ++ (vl1 ++ skipn (Z.to_nat (Int.unsigned size_v)) vldst) :: meml2) :: memll2) sendh'
      ).
      {
        eapply ipcsend_RLH_IpcSendHeap_P_preserve;
        [ | exact H38 | exact H40 | exact H31 | exact H19 ].
        unfold curcore.
        destruct Hsendh_idx; [left|right];
        destruct H36 as [? [? ?]]; repeat split; try lia.
      }

      (* EXIT_CRITICAL;ₛ *)
      eapply seq_rule.
      {
        hoare lifts (3::nil)%nat pre.
        eapply excrit1_rule'_ISnil_ISRemp'''_lg.
        {
          intros.
          unfold OldOSInvWL.
          sep pauto.
          sep name lift Aisr Ais Aier in H39.
          eapply add_aemp_isr_is_prop in H39.
          sep autocancel.
          unfold TmrInv, TmrInv', HeapInv', CoreCommuInv.
          sep normal.
          sep eexists.
          sep autocancel.
          sep split.
          exact H39.
          all: auto.
          eapply ipcsend_RLH_IpcRecvHeap_P_preserve;eauto.
          {
            rewrite H40.
            unfold curcore; lia.
          }
        }
        good_frm_sovler.
      }

      hoare abscsq; [apply noabs_oslinv |
        eapply absinfer_seq_end; eauto;
        can_change_aop_solver | ].

      (* ipcinfo ′ =ₑ ′ 0;ₛ *)
      hoare forward.

      (* 8 branch: 15 sec *)
      eapply seq_rule;
      [wzy_resolve_ternary_assign| ].
      hoare normal pre.
      pure intro.

      (* v'27 -> v'21 *)
      assert(
        v'21 = CORE0_IPC \/ v'21 = CORE1_IPC \/
        v'21 = CORE2_IPC \/ v'21 = CORE3_IPC \/
        v'21 = CORE4_IPC \/ v'21 = CORE5_IPC \/
        v'21 = CORE6_IPC \/ v'21 = CORE7_IPC
      ).
      { clear - H39. tauto. }
      clear H39.

      eapply backward_rule1;
      [eapply ipcsend_generateipc_Rv_ipcinfo;auto| ].
      pure intro.

      (* IF (flag ′ ==ₑ ′ IPC_BROAD) *)
      hoare forward. 1,2: pauto.
      { (* Branch: flag ′ ==ₑ ′ IPC_BROAD  *)
        pure intro.
        instantiate (1:= 
        (<|| END Some (V$ OS_NO_ERR) ||>  **
         p_local OSLInv tid init_lg **
         ((EX v : val, LV flag @ Int8u |-> v) **
          (EX v : val, LV size @ Int32u |-> v) **
          (EX v : val, LV srcAddr @ (Int8u) ∗ |-> v) **
          (EX v : val, LV dstCore @ Int8u |-> v) **
          (EX v : val, LV tmpsem @ os_ucos_h.OS_EVENT ∗ |-> v) **
          (EX v : val, LV step @ Int32u |-> v) **
          (EX v : val, LV ipcinfo @ Int32u |-> v) ** Aemp) **
         Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
        A_dom_lenv
          ((flag, Int8u)
           :: (size, Int32u)
              :: (srcAddr, (Int8u) ∗)
                 :: (dstCore, Int8u)
                    :: (tmpsem, os_ucos_h.OS_EVENT ∗)
                       :: (step, Int32u) :: (ipcinfo, Int32u) :: nil) ) .
        (*choose abscode broad*)
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_seq;[can_change_aop_solver | | ].
        2: eapply absinfer_choice1;[can_change_aop_solver| | intros s' Hs';exact Hs'].
        can_change_aop_solver.
        can_change_aop_solver.
        (*change abscode broad *)
        hoare abscsq; [apply noabs_oslinv | | ].
        eapply absinfer_seq;[can_change_aop_solver | | ].
        2: eapply ipcsend_absimp_generateipc_broad_choice with (x:=x); auto.
        can_change_aop_solver.
        can_change_aop_solver.
        (* GENERATEIPC (dstCore ′, ipcinfo ′ |ₑ ′ IPC_MESSAGE_BROAD);ₛ *)
        hoare forward.
        {
          (* hoare lift 2%nat pre. *)
          eapply backward_rule1;
          [ |eapply generateipc_rule].
          {
            intros.
            exact H46.
          }
          {
            can_change_aop_solver.
          }
          {
            rewrite Z2Nat.id; apply Int.unsigned_range_2.
          }
          {
            intros; split.
            {
              rewrite Z2Nat.id;
              [ |apply Int.unsigned_range_2].
              rewrite Int.repr_unsigned.
              symbolic_execution.
              clear - H4.
              destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
              apply Z.leb_gt in eq.
              exfalso; mauto.
            }
            {
              apply H42 with (z:= IPC_MESSAGE_BROAD) in H46; auto.
            }
          }
          {
            intros.
            unfold CurLINV.
            unfold p_local in H46.
            sep auto.
          }
        }

        (* ENTER_CRITICAL;ₛ *)
        
        hoare forward prim.
        unfold CoreCommuInv.
        hoare normal pre.
        pure intro.
        rename v'45 into vpthattr1.
        rename v'46 into vcspace1.
        rename v'47 into v47. 
        rename v'48 into v48. 
        rename v'49 into v49. 
        rename v'50 into v'45. 
        rename v'51 into v'46. 
        rename v'52 into v'47. 
        rename v'53 into v'48. 
        rename v'54 into v'49. 
        rename v'55 into v'50. 
        rename v'56 into v'51. 
          
        unfold AOSIPCSendSem.
        pure intro.

        (* tmpsem′ =ₑ IPCSendSem′[dstCore′];ₛ *)
        hoare forward.
        {
          clear - H5.
          destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
          eapply Z.leb_gt in eq.
          unfold CORENUM in *; exfalso; mauto.
        }
        {
          eapply isptr_list_nth_ptr; eauto.
          clear - H5. unfold CORENUM in *; lia.
        }

        (* OSTCBCur′→__OSTskSemPtr =ₑ tmpsem′;ₛ *)
        unfold EvtInv.
        hoare normal pre.
        pure intro.
        hoare lifts (25::24::45::26::nil)%nat pre.
        hoare name lift p_local pre.
        hoare name lift A_dom_lenv pre.
        hoare lifts (3::4::5::2::6::1::nil)%nat pre.
        fold init_lg.
        assert(exists p, nth_val' (Z.to_nat (Int.unsigned dstCore_v)) IPCSendSem_ptrl  = Vptr p /\ In (Vptr p) IPCSendSem_ptrl).
        {
          eapply isptr_list_nth_ptr_ex; eauto.
          lia.
        }
        destruct H56, H56.
        rewrite H56.
        eapply seq_rule.
        {
          apply SemPtr_assign_lv; auto.
        }

        pure intro.
        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        eapply absinfer_choice1; [can_change_aop_solver| |intros s' Hs';exact Hs'].
        can_change_aop_solver.

        cbn [ipcsend_before_pend].

        assert (nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v)) = Some (x0)).
        {
          pose proof nth_val'_imp_nth_val_vptr _ _ H56.
          pose proof nth_val_nth_error (Z.to_nat (Int.unsigned dstCore_v)) IPCSendSem_ptrl (Vptr x0).
          destruct H67.
          pose proof H67 H66.
          unfold IPCSendSem_ptrl in H69.
          destruct (nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v))) eqn: H70.
          {
            pose proof map_nth_error (fun x : addrval => Vptr x) (Z.to_nat (Int.unsigned dstCore_v)) OSSendSem_val H70.
            simpl in H71.
            rewrite H69 in H71.
            inversion H71. f_equal.
          }
          {
            pose proof nth_error_None OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v)).
            destruct H71.
            pose proof H71 H70.
            lia.
          }
        }
        rewrite H66.
        hoare name lift Aop curtid evptrid pre.
        hoare remember (1::2::3::nil)%nat pre.
        eapply abscsq_rule';
        [apply noabs_oslinv | | ].
        {
          eapply ipcsend_absinfer_before_pend_succ; eauto.
          subst H67.
          unfold DynamicRefactorINV, AdynrefaccfgFreeList.
          can_change_aop_solver.
        }
        subst H67.
        unfold ipcsend_sendsempend.
        rewrite H66.

        (* EXIT_CRITICAL;ₛ *)
        hoare forward prim. 
        {
          (* sep cancel Aier. *)
          unfold EvtInv, CoreCommuInv, AOSIPCSendSem, AOSMapTbl,
                 AOSUnMapTbl, AOSTCBPrioTbl, AOSRdyTblGrp, AOSRdyTbl,
                 AOSRdyGrp, AOSTime, AGVars.
          sep normal.
          sep eexists.
          sep autocancel.
          sep split.
          exact H67.
          all: try auto.
          eapply evdel_nodup_normal_semptr_preserve; eauto.
          eapply evcre_nodup_normal_semptr_preserve; eauto.
          3: eapply sem_ecb_p_semptr_normal_preserve; eauto.
          2: eapply mux_ecb_p_semptr_normal_preserve; eauto.
          1: eapply mq_ecb_p_semptr_normal_preserve; eauto.
          all: unfold CORESEM_INECB_P in H48.
          all: destruct H48, H68.
          all: unfold IPCSendSem_ptrl in H63.
          all: apply H68.
          all: pose proof in_map_iff (fun x : addrval => Vptr x) OSSendSem_val (Vptr x0).
          all: destruct H70.
          all: pose proof H70 H63.
          all: destruct H72 as [x1 [? ?]].
          all: inversion H72; subst x1; auto.
        }
        auto.
        good_frm_sovler.

        (* OSIPCSemPend (­IPCSendSem ′ [dstCore ′], ′ 0, &ₐ err ′­);ₛ *)
        assert ((Z.to_nat (Int.unsigned dstCore_v)) < 8)%nat.
        {
          clear - H5. unfold CORENUM in H5.
          replace 8%nat with (Z.to_nat 8)%Z; try lia.
        }
        (* pose proof isptr_list_nth_ptr_ex _ _ _ H54 H67 H53 as [? [? ?]]. *)
        eapply seq_rule.
        {
          eapply call_rule'.
          intuition eauto.
          4:{
            intros.
            unfold getasrt, OSSemPendPost, OSSemPendPost' in H68.
            do 6 destruct H68.
            exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val x5 :: logic_val Vnull :: nil).
            sep auto.
          }
          4:{
            intros.
            unfold getasrt, OSSemPendPre, OSSemPendPre' in H68.
            do 4 destruct H68.
            exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val x2 :: logic_val Vnull :: nil).
            sep auto.
          }
          2:{
            intros.
            unfold getasrt, OSSemPendPre, OSSemPendPre'.
            sep normal.
            exists (ipcsend_after_pend (|nil|);;
            ipcsend_postsem (Vint32 dstCore_v);; END Some (V$ OS_NO_ERR)) (Vptr x0) (V$ OS_NO_ERR) v'36.
            sep autocancel.
            sep pauto.
            2:{
              assert (nth_val 0 (Vptr x0 :: Vint32 Int.zero :: nil) = Some (Vptr x0)).
              simpl; auto.
              rewrite -> H71; auto.
            }
            exact H68.
          }
          2: good_frm_sovler.
          2: auto.
          intros.
          apply rvl_elim.
          sep get rv.
          eapply rvl_elim.
          2: apply rvl_nil.
          eapply cast_rv_tint32_tint16.
          symbolic_execution.
          auto.
        }
        
        unfold_funpost.
        hoare normal pre.
        pure intro.
        inversion H68; subst; clear H68.

        (* ENTER_CRITICAL;ₛ *)
        hoare forward prim.
        unfold EvtInv.
        hoare normal pre.
        pure intro.
        rename v'86 into vpthattr2.  
        rename v'87 into vcspace2.
        rename v'88 into v88. 
        rename v'89 into v89. 
        rename v'90 into v90. 
        rename v'91 into v'86. 
        rename v'92 into v'87. 
        rename v'93 into v'88. 
        rename v'94 into v'89. 
        rename v'95 into v'90. 
        rename v'96 into v'91. 
        rename v'97 into v'92. 
        rename v'98 into v'93. 
        rename v'99 into v'94. 
        rename v'100 into v'95. 
        rename v'101 into v'96. 
        rename v'102 into v'97. 
        rename v'103 into v'98. 
        rename v'104 into v'99. 
        rename v'105 into v'100. 
        rename v'106 into v'101. 
        rename v'107 into v'102. 
        rename v'108 into v'103. 
        rename v'109 into v'104. 
          
        (* OSTCBCur ′ .. __OSTskSemPtr =ₑ NULL;ₛ *)
        hoare name lift Aop tcbllsegevaux AOSTCBList p_local A_dom_lenv pre.
        eapply seq_rule.
        apply SemPtr_assign_null; auto.
        pure intro.

        (* after_pend *)
        hoare name lift Aop curtid evptrid pre.
        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        {
          eapply ipcsend_absinfer_after_pend_succ; eauto.
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
          all: eauto.
          eapply evdel_nodup_set_null3_preserve; eauto.
          eapply evcre_nodup_set_null3_preserve; eauto.
          eapply mq_ecb_p_set_null3_preserve; eauto.
          eapply mux_ecb_p_set_null3_preserve; eauto.
          eapply sem_ecb_p_set_null3_preserve; eauto.
        }
        auto.
        good_frm_sovler.

        (* POSTSEM( dstCore′ ) *)
        eapply forward_rule2.
        hoare name lift Aop pre.
        eapply postsem_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id.
        1,2: apply Int.unsigned_range_2.
        intros.
        rewrite Z2Nat.id;
        [ |apply Int.unsigned_range_2].
        rewrite Int.repr_unsigned.
        symbolic_execution.
        clear - H5.
        destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
        eapply Z.leb_gt in eq.
        unfold CORENUM; mauto.
        {
          intros.
          unfold CurLINV.
          unfold p_local in H81.
          sep auto.
        }
        intros.
        sep auto.
      }
      {(*Branch : flag ′ !=ₑ ′ IPC_BROAD *)
      pure intro.
      (*choose abscode rdy*)
      hoare abscsq; [apply noabs_oslinv | | ].
      eapply absinfer_seq;[can_change_aop_solver | | ].
      2: eapply absinfer_choice2;[can_change_aop_solver| | intros s' Hs';exact Hs'].
      can_change_aop_solver.
      can_change_aop_solver.
      (* GENERATEIPC spec code *)
      hoare abscsq; [apply noabs_oslinv | | ].
      {
        eapply absinfer_seq;
        [can_change_aop_solver | |
        eapply ipcsend_absimp_generateipc_rdy_choice with (x:=x); auto];
        can_change_aop_solver.
      }
      
      (* IF (flag ′ ==ₑ ′ IPC_BLOCK) *)
      hoare forward.
      {
        clear - H7.
        destruct (Int.unsigned flag_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
        apply Z.leb_gt in eq.
        unfold IPC_BROAD; exfalso.
        mauto.
      }
      {
        clear; pauto.
      }

      (* branch: IPC_BLOCK *)
      {
        instantiate (1:=
        (<|| END Some (V$ OS_NO_ERR) ||>  **
         p_local OSLInv tid init_lg **
         ((EX v : val, LV flag @ Int8u |-> v) **
          (EX v : val, LV size @ Int32u |-> v) **
          (EX v : val, LV srcAddr @ (Int8u) ∗ |-> v) **
          (EX v : val, LV dstCore @ Int8u |-> v) **
          (EX v : val, LV tmpsem @ os_ucos_h.OS_EVENT ∗ |-> v) **
          (EX v : val, LV step @ Int32u |-> v) **
          (EX v : val, LV ipcinfo @ Int32u |-> v) ** Aemp) **
         Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
        A_dom_lenv
          ((flag, Int8u)
           :: (size, Int32u)
              :: (srcAddr, (Int8u) ∗)
                 :: (dstCore, Int8u)
                    :: (tmpsem, os_ucos_h.OS_EVENT ∗)
                       :: (step, Int32u) :: (ipcinfo, Int32u) :: nil)).
      
        (* GENERATEIPC (dstCore ′, ipcinfo ′ |ₑ ′ IPC_MESSAGE_RDY) *)
        hoare forward.
        {
          hoare lift 2%nat pre.
          eapply backward_rule1;
          [ |eapply generateipc_rule].
          {
            intros.
            sep lift 2%nat in H44.
            exact H44.
          }
          can_change_aop_solver.
          rewrite Z2Nat.id.
          1,2: apply Int.unsigned_range_2.
          {
            intros; split.
            {
              rewrite Z2Nat.id;
              [ |apply Int.unsigned_range_2].
              rewrite Int.repr_unsigned.
              symbolic_execution.
              clear - H4.
              destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
              apply Z.leb_gt in eq.
              exfalso; mauto.
            }
            {
              apply H42 with (z:= IPC_MESSAGE_RDY) in H44; auto.
            }
          }
          {
            intros.
            unfold CurLINV.
            unfold p_local in H44.
            sep auto.
          }
        }

        (* ENTER_CRITICAL;ₛ *)
        hoare forward prim.
        unfold CoreCommuInv, AOSIPCSendSem.
        hoare normal pre.
        pure intro.

        (* tmpsem′ =ₑ IPCSendSem′[dstCore′];ₛ *)
        hoare forward.
        {
          clear - H5.
          destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
          eapply Z.leb_gt in eq.
          unfold CORENUM in *; exfalso; mauto.
        }
        {
          eapply isptr_list_nth_ptr; eauto.
          clear - H5. unfold CORENUM in *; lia.
        }

        (* OSTCBCur′→__OSTskSemPtr =? tmpsem′;? *)

        unfold EvtInv.
        rename v'45 into vpthattr1.
        rename v'46 into vcspace1.
        rename v'47 into v47. 
        rename v'48 into v48. 
        rename v'49 into v49. 
        rename v'50 into v'45. 
        rename v'51 into v'46. 
        rename v'52 into v'47. 
        rename v'53 into v'48. 
        rename v'54 into v'49. 
        rename v'55 into v'50. 
        rename v'56 into v'51. 
          
        hoare normal pre.
        pure intro.
        hoare lifts (25::24::45::26::nil)%nat pre.
        hoare name lift p_local pre.
        hoare name lift A_dom_lenv pre.
        hoare lifts (3::4::5::2::6::1::nil)%nat pre.
        fold init_lg.
        assert(exists p, nth_val' (Z.to_nat (Int.unsigned dstCore_v)) IPCSendSem_ptrl  = Vptr p /\ In (Vptr p) IPCSendSem_ptrl).
        {
          eapply isptr_list_nth_ptr_ex; eauto.
          lia.
        }
        destruct H57, H57.
        rewrite H57.
        eapply seq_rule.
        apply SemPtr_assign_lv; auto.

        pure intro.

        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        eapply absinfer_choice1; [can_change_aop_solver| | intros s' Hs';exact Hs'].
        can_change_aop_solver.

        cbn [ipcsend_before_pend].

        assert (nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v)) = Some (x0)).
        {
          pose proof nth_val'_imp_nth_val_vptr _ _ H57.
          (* Search (nth_val _ _ = Some _). *)
          pose proof nth_val_nth_error (Z.to_nat (Int.unsigned dstCore_v)) IPCSendSem_ptrl (Vptr x0).
          destruct H68.
          pose proof H68 H67.
          unfold IPCSendSem_ptrl in H70.
          (* Search (nth_error (map _ _) _ = Some _). *)
          destruct (nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v))) eqn: H71.
          {
            pose proof map_nth_error (fun x : addrval => Vptr x) (Z.to_nat (Int.unsigned dstCore_v)) OSSendSem_val H71.
            simpl in H72.
            rewrite H70 in H72.
            inversion H72. f_equal.
          }
          {
            pose proof nth_error_None OSSendSem_val (Z.to_nat (Int.unsigned dstCore_v)).
            destruct H72.
            pose proof H72 H71.
            lia.
          }
        }
        rewrite H67.
        hoare name lift Aop curtid evptrid pre.
        hoare remember (1::2::3::nil)%nat pre.
        eapply abscsq_rule';
        [apply noabs_oslinv | | ].
        {
          eapply ipcsend_absinfer_before_pend_succ; eauto.
          subst H68.
          can_change_aop_solver.
        }
        subst H68.
        unfold ipcsend_sendsempend.
        rewrite H67.

        (* EXIT_CRITICAL;? *)
        hoare forward prim. 
        {
          unfold EvtInv, CoreCommuInv, AOSIPCSendSem, AOSMapTbl,
                 AOSUnMapTbl, AOSTCBPrioTbl, AOSRdyTblGrp, AOSRdyTbl,
                 AOSRdyGrp, AOSTime, AGVars.
          sep normal.
          sep eexists.
          sep autocancel.
          sep split.
          exact H68.
          all: auto.
          eapply evdel_nodup_normal_semptr_preserve; eauto.
          eapply evcre_nodup_normal_semptr_preserve; eauto.
          3: eapply sem_ecb_p_semptr_normal_preserve; eauto.
          2: eapply mux_ecb_p_semptr_normal_preserve; eauto.
          1: eapply mq_ecb_p_semptr_normal_preserve; eauto.
          all: unfold CORESEM_INECB_P in H46.
          all: destruct H46, H69.
          all: unfold IPCSendSem_ptrl in H64.
          all: apply H69.
          all: pose proof in_map_iff (fun x : addrval => Vptr x) OSSendSem_val (Vptr x0).
          all: destruct H71.
          all: pose proof H71 H64.
          all: destruct H73 as [x1 [? ?]].
          all: inversion H73; subst x1; auto.
        }
        auto.
        good_frm_sovler.

        (* OSIPCSemPend (-IPCSendSem ′ [dstCore ′], ′ 0, &? err ′-);? *)
        assert ((Z.to_nat (Int.unsigned dstCore_v)) < 8)%nat.
        {
          clear - H5. unfold CORENUM in H5.
          replace 8%nat with (Z.to_nat 8)%Z; try lia.
        }
        (* pose proof isptr_list_nth_ptr_ex _ _ _ H54 H67 H53 as [? [? ?]]. *)
        eapply seq_rule.
        {
          eapply call_rule'.
          intuition eauto.
          4:{
            intros.
            unfold getasrt, OSSemPendPost, OSSemPendPost' in H69.
            do 6 destruct H69.
            exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val x5 :: logic_val Vnull :: nil).
            sep auto.
          }
          4:{
            intros.
            unfold getasrt, OSSemPendPre, OSSemPendPre' in H69.
            do 4 destruct H69.
            exists (logic_val (V$ 1)
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val Vnull
                  :: logic_val x2 :: logic_val Vnull :: nil).
            sep auto.
          }
          2:{
            intros.
            unfold getasrt, OSSemPendPre, OSSemPendPre'.
            sep normal.
            exists (ipcsend_after_pend (|nil|);;
            ipcsend_postsem (Vint32 dstCore_v);; END Some (V$ OS_NO_ERR)) (Vptr x0) (V$ OS_NO_ERR) v'36.
            sep autocancel.
            sep pauto.
            2:{
              assert (nth_val 0 (Vptr x0 :: Vint32 Int.zero :: nil) = Some (Vptr x0)).
              simpl; auto.
              rewrite -> H72; auto.
            }
            exact H69.
          }
          2: good_frm_sovler.
          2: auto.
          intros.
          apply rvl_elim.
          sep get rv.
          eapply rvl_elim.
          2: apply rvl_nil.
          eapply cast_rv_tint32_tint16.
          symbolic_execution.
          auto.
        }
        
        unfold_funpost.
        hoare normal pre.
        pure intro.
        inversion H69; subst; clear H69.

        (* ENTER_CRITICAL;? *)
        hoare forward prim.
        unfold EvtInv.
        hoare normal pre.
        pure intro.
        rename v'86 into vpthattr2.  
        rename v'87 into vcspace2.
        rename v'88 into v88. 
        rename v'89 into v89. 
        rename v'90 into v90. 
        rename v'91 into v'86. 
        rename v'92 into v'87. 
        rename v'93 into v'88. 
        rename v'94 into v'89. 
        rename v'95 into v'90. 
        rename v'96 into v'91. 
        rename v'97 into v'92. 
        rename v'98 into v'93. 
        rename v'99 into v'94. 
        rename v'100 into v'95. 
        rename v'101 into v'96. 
        rename v'102 into v'97. 
        rename v'103 into v'98. 
        rename v'104 into v'99. 
        rename v'105 into v'100. 
        rename v'106 into v'101. 
        rename v'107 into v'102. 
        rename v'108 into v'103. 
        rename v'109 into v'104. 
          

        (* OSTCBCur ′ .. __OSTskSemPtr =? NULL;? *)
        hoare name lift Aop tcbllsegevaux AOSTCBList p_local A_dom_lenv pre.
        eapply seq_rule.
        apply SemPtr_assign_null; auto.
        pure intro.

        (* after_pend *)
        hoare name lift Aop curtid evptrid pre.
        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        {
          eapply ipcsend_absinfer_after_pend_succ; eauto.
          can_change_aop_solver.
        }
        
        (* EXIT_CRITICAL;? *)
        hoare forward prim.
        {
          unfold EvtInv.
          sep normal.
          sep eexists.
          sep autocancel.
          sep split.
          exact H82.
          all: eauto.
          eapply evdel_nodup_set_null3_preserve; eauto.
          eapply evcre_nodup_set_null3_preserve; eauto.
          eapply mq_ecb_p_set_null3_preserve; eauto.
          eapply mux_ecb_p_set_null3_preserve; eauto.
          eapply sem_ecb_p_set_null3_preserve; eauto.
        }
        auto.
        good_frm_sovler.
        
        (* POSTSEM( dstCore′ ) *)
        eapply forward_rule2.
        hoare name lift Aop pre.
        eapply postsem_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id.
        1,2: apply Int.unsigned_range_2.
        intros.
        rewrite Z2Nat.id;
        [ |apply Int.unsigned_range_2].
        rewrite Int.repr_unsigned.
        symbolic_execution.
        clear - H5.
        destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
        eapply Z.leb_gt in eq.
        unfold CORENUM; mauto.
        {
          intros.
          unfold CurLINV.
          unfold p_local in H82.
          sep auto.
        }
        intros.
        sep auto.
      }
      (* branch: not IPC_BLOCK *)
      {
        instantiate (1:=
        (<|| END Some (V$ OS_NO_ERR) ||>  **
         p_local OSLInv tid init_lg **
         ((EX v : val, LV flag @ Int8u |-> v) **
          (EX v : val, LV size @ Int32u |-> v) **
          (EX v : val, LV srcAddr @ (Int8u) ∗ |-> v) **
          (EX v : val, LV dstCore @ Int8u |-> v) **
          (EX v : val, LV tmpsem @ os_ucos_h.OS_EVENT ∗ |-> v) **
          (EX v : val, LV step @ Int32u |-> v) **
          (EX v : val, LV ipcinfo @ Int32u |-> v) ** Aemp) **
         Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
        A_dom_lenv
          ((flag, Int8u)
           :: (size, Int32u)
              :: (srcAddr, (Int8u) ∗)
                 :: (dstCore, Int8u)
                    :: (tmpsem, os_ucos_h.OS_EVENT ∗)
                       :: (step, Int32u) :: (ipcinfo, Int32u) :: nil)).
        
        (* GENERATEIPC (dstCore ′, ipcinfo ′ |ₑ ′ IPC_MESSAGE_RDY) *)
        hoare forward.
        {
          hoare lift 2%nat pre.
          eapply backward_rule1;
          [ |eapply generateipc_rule].
          {
            intros.
            sep lift 2%nat in H44.
            exact H44.
          }
          can_change_aop_solver.
          rewrite Z2Nat.id.
          1,2: apply Int.unsigned_range_2.
          {
            intros; split.
            {
              rewrite Z2Nat.id;
              [ |apply Int.unsigned_range_2].
              rewrite Int.repr_unsigned.
              symbolic_execution.
              clear - H4.
              destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
              apply Z.leb_gt in eq.
              exfalso; mauto.
            }
            {
              eapply H42 in H44; eauto.
            }
          }
          {
            intros.
            unfold CurLINV.
            unfold p_local in H44.
            sep auto.
          }
        }

        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        eapply absinfer_choice2; [can_change_aop_solver| | intros s' Hs';exact Hs'].
        can_change_aop_solver.

        eapply abscsq_rule'; [apply noabs_oslinv | | ].
        eapply absinfer_seq_end.
        can_change_aop_solver.
        2:{
          intros.
          exact H44.
        }
        can_change_aop_solver.
        
        (* POSTSEM( dstCore′ ) *)
        eapply forward_rule2.
        hoare name lift Aop pre.
        eapply postsem_rule.
        can_change_aop_solver.
        rewrite Z2Nat.id.
        1,2: apply Int.unsigned_range_2.
        intros.
        rewrite Z2Nat.id;
        [ |apply Int.unsigned_range_2].
        rewrite Int.repr_unsigned.
        symbolic_execution.
        clear - H5.
        destruct (Int.unsigned dstCore_v <=? Byte.max_unsigned)%Z eqn:eq; auto.
        eapply Z.leb_gt in eq.
        unfold CORENUM; mauto.
        {
          intros.
          unfold CurLINV.
          unfold p_local in H44.
          sep auto.
        }
        intros.
        sep auto.
      } }
      hoare forward.
      hoare forward.

      pure intro.
      hoare forward.
      hoare forward.
      hoare forward.
    }
  }
Qed.
