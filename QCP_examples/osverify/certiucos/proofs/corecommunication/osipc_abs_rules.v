Require Import ucos_include.
Require Import Lia.

Require Import corecommu_rules.
Require Import corecommu_sep_added.

Open Scope code_scope.

Open Scope int_scope.

Lemma OSIpc_high_level_step_bstacknodup_abt:
 forall sch s  P bstack ,
  ~ NoDup bstack ->
   can_change_aop P ->
   sch ⊢  <|| ASSERT OSIPC_broad_nodup;; s ||> **
            Hipcbroad bstack ** P
         ⇒ <|| ABORT ||>  **
            Hipcbroad bstack ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT);[can_change_aop_solver | | ].
  instantiate (1:=
  Hipcbroad bstack ** P).
  can_change_aop_solver.
  
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros. unfold not, OSIPC_broad_nodup. intros.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  simpl in H1. simpljoin1. cbn [getabst] in *.
  assert (get o ipcbroadid = Some (osipcbroad bstack)).
  { eapply join_sig_get;eauto. }
  rewrite H1 in H2.
  inversion H2. subst x. contradiction.

  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.


Lemma OSIpc_high_level_step_bstacknodup_cont:
 forall sch s  P bstack ,
  NoDup bstack ->
   can_change_aop P ->
   sch ⊢  <|| ASSERT OSIPC_broad_nodup;; s ||> **
            Hipcbroad bstack ** P
         ⇒ <|| s ||>  **
            Hipcbroad bstack ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None);[can_change_aop_solver | | ].
  instantiate (1:=
  Hipcbroad bstack ** P).
  can_change_aop_solver.
  
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros. unfold not, OSIPC_broad_nodup. intros.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  simpl in H1. simpljoin1. cbn [getabst] in *.
  assert (get o ipcbroadid = Some (osipcbroad bstack)).
  { eapply join_sig_get;eauto. }
  eexists. split;eauto.
  eapply absinfer_seq_end;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma OSIpc_high_level_step_broad:
 forall sch s P ipcgr_val corenum_val bstack ,
  ipcgr_val&ᵢ$ IPC_MESSAGE_RDY <> $ IPC_MESSAGE_RDY ->
  ipcgr_val&ᵢ$ IPC_MESSAGE_ACK <> $ IPC_MESSAGE_ACK ->
  ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD = $ IPC_MESSAGE_BROAD ->
  Int.lt ($ -1) corenum_val = true ->
  Int.ltu corenum_val ($ 8) = true ->
  can_change_aop P ->
  sch ⊢  <|| (OSIPC_broad (|Vint32 ipcgr_val :: Vint32 corenum_val :: nil|));; s ||> **
            Hipcbroad bstack ** P
         ⇒ <|| s ||>  **
            Hipcbroad ((Z.to_nat (Int.unsigned corenum_val))::bstack) ** P.
Proof.
  intros.
  infer_solver 0%nat. 
Qed.

Lemma OSIpc_high_level_step_assume3:
 forall sch s s1 s2 s3 s4 P ipcgr_val  ,
  ipcgr_val&ᵢ$ IPC_MESSAGE_RDY <> $ IPC_MESSAGE_RDY ->
  ipcgr_val&ᵢ$ REFACTOR_RDY <> $ REFACTOR_RDY ->
  ipcgr_val&ᵢ$ IPC_MESSAGE_ACK <> $ IPC_MESSAGE_ACK ->
  ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD <> $ IPC_MESSAGE_BROAD ->
  can_change_aop P ->
  sch ⊢  <||  s1 ?? s2 ??  s3 ?? s4 ??  ASSUME (fun _ : osabst =>
                    ipcgr_val&ᵢ$ IPC_MESSAGE_RDY <> $ IPC_MESSAGE_RDY /\
                    ipcgr_val&ᵢ$ REFACTOR_RDY <> $ REFACTOR_RDY /\
                    ipcgr_val&ᵢ$ IPC_MESSAGE_ACK <> $ IPC_MESSAGE_ACK /\
                    ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD <> $ IPC_MESSAGE_BROAD);; s ||> ** P
     ⇒ <|| s ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= P);[ can_change_aop_solver | can_change_aop_solver | auto].
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= P);[ can_change_aop_solver | can_change_aop_solver | auto].
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= P);[ can_change_aop_solver | can_change_aop_solver | auto].
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= P);[ can_change_aop_solver | can_change_aop_solver | auto].
  eapply absinfer_trans with (q:= <|| END None ;; s ||> ** P) .
  eapply absinfer_seq with (q := P);[can_change_aop_solver | can_change_aop_solver |  ].
  eapply absinfer_assume;[can_change_aop_solver | can_change_aop_solver | sep auto | ].
  intros. auto.  
  apply absinfer_seq_end;[ can_change_aop_solver | can_change_aop_solver | auto].
Qed.

(* 
Lemma OSIpc_high_level_step_abt:
 forall sch s s' P ipcgr_val ipcgr_val' v'15 v'16 v'17 ct v'24 v'21 v'25 v'26 v'31 v'32 v'33 v'34 v'35 v'44 v'45,
   ipcgr_val <> ipcgr_val'->
   length v'44 = Z.abs_nat DNUM -> 
   can_change_aop P ->
   sch ⊢  <||
  ASSERT (fun O : osabst =>
           exists ipcgrl,
           get O curcoreid = Some (oscurtcore (Z.to_nat DNUM)) /\
           get O ipcgrid = Some (osipcgr ipcgrl) /\ nth_error ipcgrl (Z.to_nat DNUM) = Some (Vint32 ipcgr_val'));;s ;;s' ||> **
            HECBList v'15 **
            HTCBList v'16 **
            HTime v'17 **
            HCurTCB ct **
            HTMRList v'24 **
            HClkRate v'21 **
            HcurCore curcore **
            HCoreHeap v'25 v'26 **
            HipcsendHeap v'31 **
            HipcrecvHeap v'32 **
            Hipcsem OSIPCSem_val **
            Hipcsendsem OSSendSem_val **
            Hipcsemshared v'33 **
            Hdynfreelist v'34 **
            Hipcbroad v'35 **
            Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P 
         ⇒ <|| ABORT ||>  **
            HECBList v'15 **
            HTCBList v'16 **
            HTime v'17 **
            HCurTCB ct **
            HTMRList v'24 **
            HClkRate v'21 **
            HcurCore curcore **
            HCoreHeap v'25 v'26 **
            HipcsendHeap v'31 **
            HipcrecvHeap v'32 **
            Hipcsem OSIPCSem_val **
            Hipcsendsem OSSendSem_val **
            Hipcsemshared v'33 **
            Hdynfreelist v'34 **
            Hipcbroad v'35 **
            Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT);[can_change_aop_solver | | ].
  instantiate (1:= HECBList v'15 **
  HTCBList v'16 **
  HTime v'17 **
  HCurTCB ct **
  HTMRList v'24 **
  HClkRate v'21 **
  HcurCore curcore **
  HCoreHeap v'25 v'26 **
  HipcsendHeap v'31 **
  HipcrecvHeap v'32 **
  Hipcsem OSIPCSem_val **
  Hipcsendsem OSSendSem_val **
  Hipcsemshared v'33 ** Hdynfreelist v'34 ** Hipcbroad v'35 ** Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P).
  can_change_aop_solver.
  
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros. unfold not. intros.
  sep remember (7::16::nil)%nat in H2.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  simpl in H2. simpljoin1. cbn [getabst] in *.
  assert (sub (sig ipcgrid (osipcgr (v'44 ++ Vint32 ipcgr_val :: v'45))) o).
  { eapply sub_trans with x4. 
    eapply join_sub_l;eauto.
    eapply join_sub_r;eauto. }
  eapply sub_exists_join in H2.
  destruct H2.
  eapply join_sig_get in H2;eauto.
  rewrite H2 in H5.
  inversion H5;subst x.
  erewrite Zabs2Nat.abs_nat_nonneg in H0. 2: { clear;pose proof dnum_range. lia. }
  rewrite <- H0 in H6.
  erewrite nth_error_middle in H6.
  inversion H6.
  tryfalse.

  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma OSIpc_high_level_step_assert:
 forall sch s s' P ipcgr_val v'15 v'16 v'17 ct v'24 v'21 v'25 v'26 v'31 v'32 v'33 v'34 v'35 v'44 v'45,
   length v'44 = Z.abs_nat DNUM -> 
   can_change_aop P ->
   sch ⊢  <||
  ASSERT (fun O : osabst =>
           exists ipcgrl,
           get O curcoreid = Some (oscurtcore (Z.to_nat DNUM)) /\
           get O ipcgrid = Some (osipcgr ipcgrl) /\ nth_error ipcgrl (Z.to_nat DNUM) = Some (Vint32 ipcgr_val));;s;;s' ||> **
            HECBList v'15 **
            HTCBList v'16 **
            HTime v'17 **
            HCurTCB ct **
            HTMRList v'24 **
            HClkRate v'21 **
            HcurCore curcore **
            HCoreHeap v'25 v'26 **
            HipcsendHeap v'31 **
            HipcrecvHeap v'32 **
            Hipcsem OSIPCSem_val **
            Hipcsendsem OSSendSem_val **
            Hipcsemshared v'33 **
            Hdynfreelist v'34 **
            Hipcbroad v'35 **
            Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P 
         ⇒ <|| s;;s' ||>  **
            HECBList v'15 **
            HTCBList v'16 **
            HTime v'17 **
            HCurTCB ct **
            HTMRList v'24 **
            HClkRate v'21 **
            HcurCore curcore **
            HCoreHeap v'25 v'26 **
            HipcsendHeap v'31 **
            HipcrecvHeap v'32 **
            Hipcsem OSIPCSem_val **
            Hipcsendsem OSSendSem_val **
            Hipcsemshared v'33 **
            Hdynfreelist v'34 **
            Hipcbroad v'35 **
            Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None);[can_change_aop_solver | | ].
  instantiate (1:= HECBList v'15 **
  HTCBList v'16 **
  HTime v'17 **
  HCurTCB ct **
  HTMRList v'24 **
  HClkRate v'21 **
  HcurCore curcore **
  HCoreHeap v'25 v'26 **
  HipcsendHeap v'31 **
  HipcrecvHeap v'32 **
  Hipcsem OSIPCSem_val **
  Hipcsendsem OSSendSem_val **
  Hipcsemshared v'33 ** Hdynfreelist v'34 ** Hipcbroad v'35 ** Hipcgr (v'44 ++ Vint32 ipcgr_val :: v'45) ** P).
  can_change_aop_solver.
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  sep remember (7::16::nil)%nat in H1.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  simpl in H1. simpljoin1. cbn [getabst] in *.
  exists (v'44 ++ Vint32 ipcgr_val :: v'45).
  splits;auto.
  eapply join_sig_get;eauto.
  assert (sub (sig ipcgrid (osipcgr (v'44 ++ Vint32 ipcgr_val :: v'45))) o).
  { eapply sub_trans with x3. 
    eapply join_sub_l;eauto.
    eapply join_sub_r;eauto. }
  eapply sub_exists_join in H1.
  destruct H1.
  eapply join_sig_get;eauto.
  erewrite Zabs2Nat.abs_nat_nonneg in H. 2: { clear;pose proof dnum_range. lia. }
  rewrite <- H.
  apply nth_error_middle.

  eapply absinfer_seq_end;[can_change_aop_solver | can_change_aop_solver | auto ].
Qed.

  *)