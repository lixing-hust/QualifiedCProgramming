Require Import ucos_include.
Require Import Lia.

Open Scope code_scope.

Open Scope int_scope.

Lemma ipcsend_absimp_memcpy_succ:
  forall P size_v dstCore_v srcAddr_v flag_v
      sendh sendh' cheapl cheape cheapt step_v vl sch,
    can_change_aop P ->
    (* Int.ltu size_v ($ 1) = false ->
    Int.ltu ($ IPC_STEP) size_v = false ->
    Int.ltu ($ CORENUM -ᵢ $ 1) dstCore_v = false ->
    Int.eq dstCore_v ($ DNUM) = false ->
    Int.ltu ($ IPC_BROAD) flag_v = false ->
    Int.eq flag_v ($ IPC_BROAD) = false -> *)
    (* Int.ltu dstCore_v ($ DNUM) = true -> *)
    In_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) ->
    Get_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) vl ->
    step_v = (Z.to_nat (Int.unsigned dstCore_v) - 
      (if Z.to_nat DNUM <? Z.to_nat (Int.unsigned dstCore_v) then 1 else 0))%nat ->
    (* ((Int.unsigned dstCore_v > DNUM)%Z /\ stepz = DNUM \/
    (Int.unsigned dstCore_v < DNUM)%Z /\ stepz = (DNUM - 1)%Z) -> *)
    set_sendheap step_v sendh (Z.to_nat (Int.unsigned size_v)) vl sendh' ->
    absinfer sch
    ( <||
        ipcsend_memcpy
        (Vint32 dstCore_v
          :: Vptr srcAddr_v :: Vint32 size_v :: Vint32 flag_v :: nil)
      ||> ** 
      HipcsendHeap sendh **
      HCoreHeap cheapl cheape cheapt **
      P)
    ( <|| END None ||> **
      HipcsendHeap sendh' **
      HCoreHeap cheapl cheape cheapt **
      P).
Proof.
  intros.
  infer_solver 0%nat.
Qed.

Lemma ipcsend_absimp_memcpy_fail:
  forall P size_v dstCore_v srcAddr_v flag_v
         cheapl cheape cheapt sch,
    can_change_aop P ->
    ~ In_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) ->
    absinfer sch
    ( <||
        ipcsend_memcpy
        (Vint32 dstCore_v
          :: Vptr srcAddr_v :: Vint32 size_v :: Vint32 flag_v :: nil)
      ||> ** 
      HCoreHeap cheapl cheape cheapt **
      P)
    ( <|| ABORT ||> **
      HCoreHeap cheapl cheape cheapt **
      P).
Proof.
  intros.
  unfold ipcsend_memcpy.
  eapply absinfer_trans;
  [eapply absinfer_choice2;
  [can_change_aop_solver| |intros s Hs; exact Hs]| ].
  { can_change_aop_solver. }
  eapply absinfer_abt;
  [can_change_aop_solver|can_change_aop_solver| ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  {
    simpl_subst_gamma.
    hmstep_call_consturctor;
    [eapply spec_prim_step_abt| ].
    {
      unfolds. split;eauto.
      exists dstCore_v srcAddr_v size_v flag_v.
      splits;try eauto. instantiate (1:=O).
      exists cheapl cheape.
      simpl in H1.
      simpljoin1.
      eapply join_sig_get in H4;
      eauto.
    }
    {
      instantiate (1:= empabst). 
      apply map_join_emp.
    }
    {
      repeat hmstep_call_consturctor.
    }
  }
  {
    simpl in *.
    simpljoin.
    repeat progress  (do 6 eexists;
    splits ; try eauto).
    eapply change_aop_rule; eauto.
  }
Qed.

Ltac my_infer_branch n:=
  match n with
  | O => match goal with
         | |- absinfer _ (<|| _ ?? _ ||> ** _) _ =>
            eapply absinfer_choice1; auto
         | _ => eapply absinfer_eq
        end
  | S ?n' =>
    eapply absinfer_trans;
    [
      eapply absinfer_choice2; auto;
      [ |let H:=fresh "H" in intros ? H; exact H]; auto|
      my_infer_branch n'
    ]
  end.

Lemma ipcsend_absimp_generateipc_rdy_choice:
  forall sch dst x P,
  can_change_aop P ->
  x = 0%nat \/
  x = 1%nat \/
  x = 2%nat \/
  x = 3%nat \/ x = 4%nat \/ x = 5%nat \/ x = 6%nat \/ x = 7%nat ->
  absinfer sch
    (<|| ipcsend_generateipc_rdy (Vint32 dst) ||> ** P)
    (<|| coreint (Z.to_nat (Int.unsigned dst)) (Vint32 (IPCINFO_brach x IPC_MESSAGE_RDY))||> ** P).
Proof.
  intros.
  unfold ipcsend_generateipc_rdy.
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

Lemma refactsend_absimp_memcpy_fail:
  forall P size_v dstCore_v srcAddr_v
         cheapl cheape cheapt sch,
    can_change_aop P ->
    ~ In_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) ->
    absinfer sch
    ( <||
        refactsend_memcpy
        (Vint32 dstCore_v
          :: Vptr srcAddr_v :: Vint32 size_v :: nil)
      ||> ** 
      HCoreHeap cheapl cheape cheapt **
      P)
    ( <|| ABORT ||> **
      HCoreHeap cheapl cheape cheapt **
      P).
Proof.
  intros.
  unfold refactsend_memcpy.
  eapply absinfer_trans;
  [eapply absinfer_choice2;
  [can_change_aop_solver| |intros s Hs; exact Hs]| ].
  { can_change_aop_solver. }
  eapply absinfer_abt;
  [can_change_aop_solver|can_change_aop_solver| ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  {
    simpl_subst_gamma.
    hmstep_call_consturctor;
    [eapply spec_prim_step_abt| ].
    {
      unfolds. split;eauto.
      exists dstCore_v srcAddr_v size_v.
      splits;try eauto. instantiate (1:=O).
      exists cheapl cheape.
      simpl in H1.
      simpljoin1.
      eapply join_sig_get in H4;
      eauto.
    }
    {
      instantiate (1:= empabst). 
      apply map_join_emp.
    }
    {
      repeat hmstep_call_consturctor.
    }
  }
  {
    simpl in *.
    simpljoin.
    repeat progress  (do 6 eexists;
    splits ; try eauto).
    eapply change_aop_rule; eauto.
  }
Qed.

Lemma refactsend_absimp_memcpy_succ:
  forall P size_v dstCore_v srcAddr_v 
      sendh sendh' cheapl cheape cheapt step_v vl sch,
    can_change_aop P ->
    In_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) ->
    Get_heapl_addrval cheapl srcAddr_v
      (Z.to_nat (Int.unsigned size_v)) vl ->
    step_v = (Z.to_nat (Int.unsigned dstCore_v) - 
      (if Z.to_nat DNUM <? Z.to_nat (Int.unsigned dstCore_v) then 1 else 0))%nat ->
    set_sendheap step_v sendh (Z.to_nat (Int.unsigned size_v)) vl sendh' ->
    absinfer sch
    ( <||
        refactsend_memcpy
        (Vint32 dstCore_v
          :: Vptr srcAddr_v :: Vint32 size_v  :: nil)
      ||> ** 
      HipcsendHeap sendh **
      HCoreHeap cheapl cheape cheapt **
      P)
    ( <|| END None ||> **
      HipcsendHeap sendh' **
      HCoreHeap cheapl cheape cheapt **
      P).
Proof.
  intros.
  infer_solver 0%nat.
Qed.

Lemma refactsend_absimp_generateipc_refactor_rdy:
  forall sch dst x P,
  can_change_aop P ->
  x = 0%nat \/
  x = 1%nat \/
  x = 2%nat \/
  x = 3%nat \/ x = 4%nat \/ x = 5%nat \/ x = 6%nat \/ x = 7%nat ->
  absinfer sch
    (<|| refactsend_generateipc_refactor_rdy (Vint32 dst) ||> ** P)
    (<|| coreint (Z.to_nat (Int.unsigned dst)) (Vint32 (IPCINFO_brach x REFACTOR_RDY))||> ** P).
Proof.
  intros.
  unfold refactsend_generateipc_refactor_rdy.
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