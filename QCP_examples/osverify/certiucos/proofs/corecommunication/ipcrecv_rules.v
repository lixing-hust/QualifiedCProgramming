Require Import ucos_include.
Require Import Lia.

(* Require Import sep_combine_lemmas_added. *)
Require Import corecommu_rules.
Require Import corecommu_sep_added.

Open Scope code_scope.

Open Scope int_scope.
    
Lemma IPCrecv_high_level_step_invalid :
  forall P sch x1 i1 i i0 s,
     x1 = Vnull \/
     Int.ltu i1 ($ 1) = true \/
     Int.ltu ($ IPC_STEP) i1 = true \/
     Int.ltu ($ CORENUM -ᵢ $ 1) i = true \/
     Int.eq i ($ DNUM) = true \/
     Int.ltu ($ IPC_BROAD) i0 = true ->
    can_change_aop P ->
     sch    ⊢   ( <||
     ipcrecv_err_invalid (|Vint32 i :: x1 :: Vint32 i1 :: Vint32 i0 :: nil|)
     ?? s ||> **  P) ⇒
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P)  .
Proof.
  infer_solver 0%nat. 
Qed. 

Lemma IPCrecv_high_level_step_broad_assert_abt :
  forall i p i2 i1 i0 v sch P s ecbl tcbl tid cheapl cheape cheapt sendh recvh broad_stack broad_stack',
   Int.eq i0 ($ IPC_BROAD) = true ->
   broad_stack = Z.to_nat (Int.unsigned i2) :: broad_stack' ->
   v <> Vint32 i2->
   can_change_aop P ->
   sch ⊢ <|| ipcrecv_broad_error
            (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|) ?? ASSERT ipcrecv_middelval v ;; s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack ** P  ⇒
          <|| ABORT ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt**
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack ** P.
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s' Hs';exact Hs'].
  1,2: can_change_aop_solver.

  eapply absinfer_trans.
  eapply absinfer_seq with (s1':= ABORT).
  
  3: eapply absinfer_assert_abt; [  | | intros s' Hs';exact Hs' | .. ].
  1,2,3,4: can_change_aop_solver.
  2: eapply absinfer_seq_abt;[can_change_aop_solver|can_change_aop_solver|sep auto].

  intros.
  unfold not, ipcrecv_middelval.
  intro.
  destruct v;auto.

  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?].
  cbn [getabst] in *.
  rewrite H0 in *.
  destruct H4 as [? [? [? ?]]].
  subst x.
  
  sep remember (11::nil)%nat in H3.
  simpl_sat H3. simpljoin1.
  assert (get o ipcbroadid = Some (osipcbroad (Z.to_nat (Int.unsigned i2) :: broad_stack'))).
  { eapply join_sig_get;eauto. }

  pose proof map_get_unique H0 H4.
  inversion H3.
  eapply Z2Nat.inj_iff in H7. 2,3: (apply Int.unsigned_range).
  apply unsigned_inj in H7.
  tryfalse.
Qed.

Lemma IPCrecv_high_level_step_broad_assert_cont :
  forall i p i2 i1 i0 sch P s ecbl tcbl tid cheapl cheape cheapt sendh recvh broad_stack broad_stack',
   Int.eq i0 ($ IPC_BROAD) = true ->
   broad_stack = Z.to_nat (Int.unsigned i2) :: broad_stack' ->
   can_change_aop P ->
   sch ⊢ <|| ipcrecv_broad_error
            (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 ::  Vint32 i2 :: nil|) ??ASSERT ipcrecv_middelval ( Vint32 i2) ;; s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack ** P  ⇒
          <|| s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack ** P.
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2;[ | | intros s' Hs';exact Hs'].
  1,2: can_change_aop_solver.

  eapply absinfer_trans.
  eapply absinfer_seq.
  
  3: eapply absinfer_assert_cont; [  | | intros s' Hs';exact Hs' | .. ].
  1,2,3,4: can_change_aop_solver.
  2: eapply absinfer_seq_end;[can_change_aop_solver|can_change_aop_solver|sep auto].

  intros.
  unfold ipcrecv_middelval.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?].
  cbn [getabst] in *.
  rewrite H0 in *.
  sep remember (11::nil)%nat in H2.
  simpl_sat H2. simpljoin1.
  assert (get o ipcbroadid = Some (osipcbroad (Z.to_nat (Int.unsigned i2) :: broad_stack'))).
  { eapply join_sig_get;eauto. }
  do 2 eexists.
  split;eauto.
Qed.

Lemma IPCrecv_high_level_step_broad_error :
  forall i p i1 i0 v sch P s ecbl tcbl tid cheapl cheape cheapt sendh recvh,
   Int.eq i0 ($ IPC_BROAD) = true ->
   can_change_aop P ->
   sch ⊢ <|| ipcrecv_broad_error
            (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|) ?? s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad error_broad_stack ** P  ⇒
          <|| END (Some (V$ EBUSY)) ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad error_broad_stack ** P.
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1;[ | | intros s' Hs';exact Hs'].
  1,2: can_change_aop_solver.

  eapply absinfer_prim.
  1,2: can_change_aop_solver.
  
  unfolds;intros.
  eexists;exgamma.
  splits.
  { 
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { assert (get O ipcbroadid = Some (osipcbroad error_broad_stack)).
    { sep remember (11::nil)%nat in H1.
    simpl_sat H1;simpljoin1.
    eapply join_sig_get;eauto. }
    eapply spec_prim_step.
    4: eapply map_join_emp.
    unfold ipcrecv_broad_error.
    splits;eauto.
    do 5 eexists.
    splits;eauto.
    cbn;auto.
    cbn;auto.
    eapply map_join_emp. }
  hmstep_call_consturctor. }
  sep auto.
Qed.

Lemma IPCrecv_high_level_step_broad_nil :
  forall i p i1 i0 v sch P s ecbl tcbl tid cheapl cheape cheapt sendh recvh (*dynl*),
   Int.eq i0 ($ IPC_BROAD) = true ->
   can_change_aop P ->
   sch ⊢ <|| ipcrecv_broad_error
            (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: v :: nil|) ?? s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad nil ** P  ⇒
          <|| END (Some (V$ EBUSY)) ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad nil ** P.
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1;[ | | intros s' Hs';exact Hs'].
  1,2: can_change_aop_solver.

  eapply absinfer_prim.
  1,2: can_change_aop_solver.
  
  unfolds;intros.
  eexists;exgamma.
  splits.
  { 
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { assert (get O ipcbroadid = Some (osipcbroad nil)).
    { sep remember (11::nil)%nat in H1.
    simpl_sat H1;simpljoin1.
    eapply join_sig_get;eauto. }
    eapply spec_prim_step.
    4: eapply map_join_emp.
    unfold ipcrecv_broad_error.
    splits;eauto.
    do 5 eexists.
    splits;eauto.
    cbn;auto.
    cbn;auto.
    eapply map_join_emp. }
  hmstep_call_consturctor. }
  sep auto.
Qed.

Lemma IPCrecv_high_level_step_broad :
  forall i p i1 i0 i2 sch P s ecbl tcbl tid cheapl cheape cheapt sendh recvh broad_stack broad_stack',
   Int.eq i0 ($ IPC_BROAD) = true ->
   broad_stack = Z.to_nat (Int.unsigned i2)::broad_stack'  ->
   can_change_aop P ->
   sch ⊢ <|| ipcrecv_broad (|Vint32 i :: Vptr p :: Vint32 i1 :: Vint32 i0 :: Vint32 i2 :: nil|) ;; s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack ** P  ⇒
          <|| s ||> **
          HECBList ecbl **
          HTCBList tcbl **
          HCurTCB tid **
          HcurCore curcore **
          HCoreHeap cheapl cheape cheapt **
          HipcsendHeap sendh **
          HipcrecvHeap recvh **
          Hipcsem OSIPCSem_val **
          Hipcsendsem OSSendSem_val **
          Hipcsemshared OSSemShared_val **
          Hipcbroad broad_stack' ** P.
Proof. 
  intros. subst broad_stack.
  infer_solver 0%nat. 
Qed.

Lemma IPCrecv_high_level_step_memcpy_abt:
forall coreheapl cheapt dstAddr_l size_v P sch i0 v s v'55 v'56 tid v'65 v'70 v'71 i , 
~ In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v)) ->
can_change_aop P ->
sch  ⊢  <||
  ipcrecv_memcpy
  (|Vint32 i :: Vptr dstAddr_l :: Vint32 size_v :: Vint32 i0 :: v:: nil|);;s ||>  **
  HECBList v'55 **
  HTCBList v'56 **
  HCurTCB tid **
  HcurCore curcore **
  HCoreHeap coreheapl v'65 cheapt ** 
  HipcsendHeap v'70 **
  HipcrecvHeap v'71 ** P ⇒ <|| ABORT ||>  **
  HECBList v'55 **
  HTCBList v'56 **
  HCurTCB tid **
  HcurCore curcore **
  HCoreHeap coreheapl v'65 cheapt ** 
  HipcsendHeap v'70 **
  HipcrecvHeap v'71 ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT);[can_change_aop_solver | | ].
  instantiate (1:=HECBList v'55 **
  HTCBList v'56 **
  HCurTCB tid **
  HcurCore curcore ** HCoreHeap coreheapl v'65 cheapt
  ** HipcsendHeap v'70 **
  HipcrecvHeap v'71 ** P).
  can_change_aop_solver.
  eapply absinfer_abt; try (eauto || can_change_aop_solver).
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  unfolds. split;eauto.
  exists i dstAddr_l size_v i0 v curcore .
  splits;try eauto. instantiate (1:= O). 
  { sep remember (4::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
  exists v'71 coreheapl v'65 cheapt.
  splits;try eauto. 
  { sep remember (7::nil)%nat in H1. simpl in H1. simpljoin1. 
  eapply join_sig_get;eauto.  }
  { sep remember (5::nil)%nat in H1. simpl in H1. simpljoin1. 
  eapply join_sig_get;eauto.  }
  instantiate (1:= empabst). 
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  simpl in *.
  simpljoin.
  repeat progress  (do 6 eexists;
  splits ; try eauto).
  eapply change_aop_rule; eauto. 

  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma IPCrecv_high_level_step_memcpy_succ:
  forall coreheapl cheapt dstAddr_l size_v P sch i0 v srccore_v v'55 v'56 tid v'65 v'70 v'71 i s stepn vlsrc cHeapl', 
  In_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v)) ->
  (Int.eq i0 ($ IPC_BROAD) = false /\ srccore_v = i \/
     Int.eq i0 ($ IPC_BROAD) = true /\
     (exists i2,
      srccore_v = i2 /\
      v = Vint32 i2 /\
      (Int.unsigned i2 <= 7)%Z /\ Int.eq i2 ($ DNUM) = false)) ->
  stepn = compute_step (Z.to_nat (Int.unsigned srccore_v)) curcore ->
  nth_error v'71 stepn = Some vlsrc ->
  update_heapl_addrval coreheapl dstAddr_l (Z.to_nat (Int.unsigned size_v)) (firstn (Z.to_nat(Int.unsigned size_v)) vlsrc) cHeapl'->
  can_change_aop P ->
  sch  ⊢  <||
  ipcrecv_memcpy(|Vint32 i :: Vptr dstAddr_l :: Vint32 size_v :: Vint32 i0 :: v :: nil|);; s||>  **
  HECBList v'55 **
  HTCBList v'56 **
  HCurTCB tid **
  HcurCore curcore **
  HCoreHeap coreheapl v'65 cheapt ** 
  HipcsendHeap v'70 **
  HipcrecvHeap v'71 ** P ⇒ 
  <|| s ||>  **
  HECBList v'55 **
  HTCBList v'56 **
  HCurTCB tid **
  HcurCore curcore **
  HCoreHeap cHeapl' v'65 cheapt ** 
  HipcsendHeap v'70 **
  HipcrecvHeap v'71 ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3: { eapply absinfer_seq_end.
       instantiate (1:= HECBList v'55 **
       HTCBList v'56 **
       HCurTCB tid **
       HcurCore curcore **
       HCoreHeap cHeapl' v'65 cheapt **
       HipcsendHeap v'70 ** HipcrecvHeap v'71 ** P).
       can_change_aop_solver.
       can_change_aop_solver.
       sep auto. }
   can_change_aop_solver.
   tri_infer_prim; eexists;exgamma. 
   splits.
   {
   simpl_subst_gamma.
   repeat hmstep_call_consturctor.
   instantiate (1:= set O oscoreheapid (oscoreheap (cHeapl', v'65, cheapt))).
   unfold ipcrecv_memcpy. splits;eauto.
   exists i dstAddr_l size_v i0 v curcore.
   splits;eauto.  
   { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
   exists v'71 coreheapl v'65 cheapt.
   splits;eauto.
   { sep remember (7::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
   { sep remember (5::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
   left.
   destruct H0 as [[? ?] | [? [? [? [? ?]]]]];subst srccore_v.
   { left;splits;auto. 
   exists stepn vlsrc cHeapl'.
   splits;auto. }
   { right;splits;auto.
     exists x. split;auto.
    exists stepn vlsrc cHeapl'.
    splits;auto. } 
  1,2: try absinfer_side_condition_solver.
  1,2: apply map_join_emp. }
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma IPCrecv_high_level_step_nonack: 
 forall flag_v sch P s v,
 Int.eq flag_v ($ IPC_NONACK) = true -> 
 can_change_aop P ->
 sch  ⊢  <|| (ASSUME ipcrecv_nonack (Vint32 flag_v)?? s);; END  Some v||>  ** P ⇒ 
 <|| END  Some v ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= P);auto.
  eapply absinfer_choice1 with (q:= P);auto.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:=P);auto.
  apply absinfer_assume;auto.
  apply absinfer_seq_end;auto.
Qed.

Lemma IPCrecv_high_level_step_ack: 
 forall flag_v sch P s v,
 can_change_aop P ->
 sch  ⊢  <|| (ASSUME ipcrecv_nonack (Vint32 flag_v)?? s);; END  Some v||>  ** P ⇒ 
 <|| s;;END  Some v ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= P);auto.
  eapply absinfer_choice2 with (q:= P);auto.
  apply absinfer_eq.
Qed.

Ltac infer_choice n:=
    match n with 
    | 0%nat => (apply absinfer_eq ||
              apply absinfer_choice1;auto)
    | S ?n' => match goal with 
      |H : can_change_aop ?p |- _ =>  eapply absinfer_trans;[apply absinfer_choice2 with (q:= p);auto| infer_choice n' ]
      end
    end.

Lemma IPCrecv_high_level_step_choose_ipcinfo :
 forall n sch P srccore_v i dstAddr_l size_v flag_v v rv,
 (Z.to_nat DNUM = n)%nat ->
 (Int.eq flag_v ($ IPC_BROAD) = false /\ srccore_v = i \/
     Int.eq flag_v ($ IPC_BROAD) = true /\
     (exists i2,
      srccore_v = i2 /\
      v = Vint32 i2 /\
      (Int.unsigned i2 <= 7)%Z /\ Int.eq i2 ($ DNUM) = false)) -> 
 can_change_aop P ->
 sch  ⊢  <||  ipcrecv_succ_ack (Vint32 i :: Vptr dstAddr_l :: Vint32 size_v :: Vint32 flag_v :: v :: nil);; END  Some rv||>  ** P ⇒ 
 <|| coreint (Z.to_nat (Int.unsigned srccore_v)) (Vint32 (IPCINFO_case n));;END  Some rv ||>  ** P.
Proof.
  intros.
  eapply absinfer_seq;auto.
  pose proof DNUM_destruct.
  unfold ipcrecv_succ_ack. 
  destruct H0 as [[H0 ?] | [H0 [? [? [? [? ?]]]]]];
  rewrite H0;subst srccore_v;try (subst v).
  destruct H2 as [Hd | [Hd | [Hd | [Hd |[Hd | [Hd | [Hd | Hd]]]]]]]; rewrite Hd in H;subst n.
  infer_choice 0%nat.
  infer_choice 1%nat.
  infer_choice 2%nat.
  infer_choice 3%nat.
  infer_choice 4%nat.
  infer_choice 5%nat.
  infer_choice 6%nat.
  infer_choice 7%nat.

  destruct H2 as [Hd | [Hd | [Hd | [Hd |[Hd | [Hd | [Hd | Hd]]]]]]]; rewrite Hd in H;subst n.
  infer_choice 0%nat.
  infer_choice 1%nat.
  infer_choice 2%nat.
  infer_choice 3%nat.
  infer_choice 4%nat.
  infer_choice 5%nat.
  infer_choice 6%nat.
  infer_choice 7%nat.
Qed.

   

