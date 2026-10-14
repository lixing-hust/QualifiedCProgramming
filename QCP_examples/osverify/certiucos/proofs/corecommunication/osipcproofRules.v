Require Import ucos_include.
Require Import Lia.

Require Import sem_lab.
Require Import ternary_assignment.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.

Lemma OSIpc_proofPart0 : 
forall p' r
(ct: tid)
(s' : spec_code)
(ipcgr_val: int32),
can_change_aop p' ->
{|OS_spec, GetHPrio, OSLInv, I, r,
Afalse|}|- ct
{{ <||
  clearipc (Z.to_nat DNUM) (Vint32 ipcgr_val);; s' ||>  **
  GV iIPCGRInfo @ (long) ∗ |-> Vptr ipcgr_addr **
  PV ipcgr_addr @ long |-> Vint32 ipcgr_val **
  Hipcgr ipcgr_val **
  LV read_ipcgr @ long |-> Vint32 ipcgr_val **
  p_local OSLInv ct init_lg **
  p' }} 
CLEARIPC (〈 Int8u 〉 ′ DNUM, read_ipcgr ′)
{{ <|| s' ||>  **
  GV iIPCGRInfo @ (long) ∗ |-> Vptr ipcgr_addr **
  PV ipcgr_addr @ long |-> Vint32 Int.zero **
  Hipcgr Int.zero **
  LV read_ipcgr @ long |-> Vint32 ipcgr_val **
  p_local OSLInv ct init_lg **
  p' }} .
Proof.
  intros.
  hoare normal pre.
  pure intro.
  eapply forward_rule2.
  eapply clearipc_rule.
  4: { intros. sep lifts (2::3::nil)%nat in H0. exact H0. }
  can_change_aop_solver.
  { clear.
    pose proof dnum_range.
    unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize.
    simpl.
    lia. }
  { split.
    { symbolic_execution.
      pose proof dnum_range as [h1 h2]. 
      erewrite Z2Nat.id by lia.
      clear - h1 h2. 
      erewrite inline_bittblfunctions.mutexpost_intlemma1 by mauto.
      auto. }
    symbolic_execution. }
  { intros. sep lift 3%nat in H. unfold p_local, CurLINV in *.
    sep auto.  }
  intros.
  sep auto.
Qed.

Lemma OSIpc_proofPart1 : 
forall p' r  ier isr  si i
(ct: tid)
(v'1: val)
(aop: spec_code)
(corenum_val: int32)
(ipcgr_val: int32),
    GoodFrm p' ->
    isr_is_prop (isrupd isr i true) (i :: si) ->
    ipcgr_val&ᵢ$ CORE0_IPC = $ CORE0_IPC /\
    DNUM <> 0 /\ corenum_val = $ 0 \/
    ipcgr_val&ᵢ$ CORE0_IPC <> $ CORE0_IPC /\
    (ipcgr_val&ᵢ$ CORE1_IPC = $ CORE1_IPC /\
     DNUM <> 1 /\ corenum_val = $ 1 \/
     ipcgr_val&ᵢ$ CORE1_IPC <> $ CORE1_IPC /\
     (ipcgr_val&ᵢ$ CORE2_IPC = $ CORE2_IPC /\
      DNUM <> 2 /\ corenum_val = $ 2 \/
      ipcgr_val&ᵢ$ CORE2_IPC <> $ CORE2_IPC /\
      (ipcgr_val&ᵢ$ CORE3_IPC = $ CORE3_IPC /\
       DNUM <> 3 /\ corenum_val = $ 3 \/
       ipcgr_val&ᵢ$ CORE3_IPC <> $ CORE3_IPC /\
       (ipcgr_val&ᵢ$ CORE4_IPC = $ CORE4_IPC /\
        DNUM <> 4 /\ corenum_val = $ 4 \/
        ipcgr_val&ᵢ$ CORE4_IPC <> $ CORE4_IPC /\
        (ipcgr_val&ᵢ$ CORE5_IPC = $ CORE5_IPC /\
         DNUM <> 5 /\ corenum_val = $ 5 \/
         ipcgr_val&ᵢ$ CORE5_IPC <> $ CORE5_IPC /\
         (ipcgr_val&ᵢ$ CORE6_IPC = $ CORE6_IPC /\
          DNUM <> 6 /\ corenum_val = $ 6 \/
          ipcgr_val&ᵢ$ CORE6_IPC <> $ CORE6_IPC /\
          (ipcgr_val&ᵢ$ CORE7_IPC = $ CORE7_IPC /\
           DNUM <> 7 /\ corenum_val = $ 7 \/
           ipcgr_val&ᵢ$ CORE7_IPC <> $ CORE7_IPC /\
           corenum_val = $ -1)))))))  ->
{|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|- ct
{{ <|| aop ||>  **
  Aisr (isrupd isr i true) **
  ([|i = 1%nat|] ** Aier (ierupd ier i false) \\// [|i <> 1%nat|] ** Aier (ierupd ier i true)) **
  Aie false **
  Ais (i :: si) **
  Acs nil **
  p_local OSLInv ct init_lg **
  LV corenum @ long |-> v'1 **
  LV read_ipcgr @ long |-> Vint32 ipcgr_val **
  p' }} 
  corenum ′ =ᶠ OS_getCoreIPC (·read_ipcgr ′·)
{{ <|| aop ||>  **
  Aisr (isrupd isr i true) **
  ([|i = 1%nat|] ** Aier (ierupd ier i false) \\// [|i <> 1%nat|] ** Aier (ierupd ier i true)) **
  Aie false **
  Ais (i :: si) **
  Acs nil **
  p_local OSLInv ct init_lg **
  LV corenum @ Int32u |-> Vint32 corenum_val **
  LV read_ipcgr @ Int32u |-> Vint32 ipcgr_val **
  p' }} .
Proof.
  intros.
  eapply forward_rule2.
  hoare_calle_lvar.
  instantiate (1:= logic_isr isr
  :: logic_ier ier :: logic_ie false :: logic_is si :: logic_hid i :: logic_code aop :: nil). reflexivity.
  good_frm_sovler.
  { unfold retpost, OS_getCoreIPCPost, OS_getCoreIPCPost'.
    cbn [getasrt].
    intros.
    sep destruct H2. sep split in H2.
    do 8 (destruct H6 as [ [? [? ?] ]|[? H6] ];[subst v;auto | ]).
    subst v;auto.  }
  { intros.
    exists init_lg.
    sep auto. }
  { intros.
    exists init_lg.
    sep auto. }

  intros.
  destruct H2.
  unfold OS_getCoreIPCPost, getasrt, OS_getCoreIPCPost' in H2.
  sep normal in H2.
  sep destruct H2.
  sep lifts (8::9::nil)%nat in H2.
  apply sep_pure_split in H2 as [? H2].
  apply sep_pure_split in H2 as [? H2].
  inverts H3.
  inverts H4.
  trycancel.
  sep auto.
  assert (x = Vint32 corenum_val).
  { clear - H1 H4.
    repeat (match goal with 
    | H : _ \/ _  |- _ => destruct H 
    | H : _ /\ _  |- _ => destruct H
    | H : corenum_val = _ |- _ => subst corenum_val 
    | H: Some x = Some _ |- _ => inverts H 
    end);auto;tryfalse. }
  subst x.
  exact H2.
Qed. 