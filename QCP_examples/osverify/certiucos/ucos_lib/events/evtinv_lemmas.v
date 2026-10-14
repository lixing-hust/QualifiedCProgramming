Require Import include_frm.
Require Import ifun_spec.
Require Import os_code_defs.
Require Import os_inv.
Require Import seplog_tactics.
Require Import ucos_frmaop.
Require Import gjb_common.
Require Import evaux_pure. 

Definition EvtInv_part1 ecbls tcbls :=
  (EX ectrl osql qblkl msgql,
                    AOSQFreeList osql ** 
                    AOSQFreeBlk qblkl ** (* free lists *)
                    AECBList ectrl msgql ecbls  tcbls ** (* msgq *)
                    HECBList ecbls).

Definition EvtInv_part2 ecbls tcblh tcbvl (vhold: addrval) (scapl mcapl qcapl : list vallist) :=

  (EX fecbh eventl evatoms evstructs evarrays
      sinfol minfol qattrl semeibs muxeibs qeibs pbls ebls locmp ptrmp,
   
                    AOSEventFreeList fecbh eventl **

                    Hebls ebls ** AErrblkList ebls **
                    Hpbls pbls ** APosblkList pbls **
                    HEvAtomHeap evatoms **  AEvAtomHeap evatoms **
                    HEvStructHeap evstructs **  AEvStructHeap evstructs **
                    HEvArrayHeap evarrays **  AEvArrayHeap evarrays **
                    [| R_Q_Data_P evstructs evarrays |] **
                    HSEMInfo semeibs ** ASemEIBs sinfol scapl semeibs ecbls vhold ** 
                    HMuxInfo muxeibs ** AMuxEIBs minfol mcapl muxeibs ecbls vhold **
                    HQAttr qeibs ** AMqEIBs qattrl qcapl qeibs ecbls vhold ** 
                    [| vhold = vhold_addr |] ** 
                    [| SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs |] **
                    [| evcre_nodup locmp ptrmp |] ** 
                    [| evdel_nodup locmp ptrmp |] ** 
                    [| eibref_distinct semeibs muxeibs qeibs |] **
                    HEvLoc locmp ** HEvPtr ptrmp ** 
                    tcbllsegevaux tcblh tcbvl locmp ptrmp).

Ltac trycancel_EvtInv1 :=
try sep cancel AOSQFreeList;
try sep cancel AOSQFreeBlk;
try sep cancel AECBList;
try sep cancel absecblist.

Ltac trycancel_EvtInv2 :=
try sep cancel AOSEventFreeList;
try sep cancel ASemEIBs;
try sep cancel AMuxEIBs;
try sep cancel AMqEIBs;
try sep cancel tcbllsegevaux;
try sep cancel ASeminfo;
try sep cancel APthreadMutex;
try sep cancel AMqAttr;
try sep cancel ASeminfo;
try sep cancel ASemCap;
try sep cancel llsegevaux.

Ltac trycancel_EvtInv :=
trycancel_EvtInv1; trycancel_EvtInv2.

Lemma EvtInv_eq:
forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl,
    EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl <==> EvtInv_part1 ecbls tcbls ** EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl.
Proof.
unfold EvtInv.
unfold EvtInv_part1.
unfold EvtInv_part2.
intros.
split; introv Hsat; sep auto.
Qed.

Lemma fold_EvtInv_part1:
forall s P ecbls osql qblkl ectrl msgql tcbls,
   s |= AOSQFreeList osql ** AOSQFreeBlk qblkl **
          AECBList ectrl msgql ecbls tcbls ** HECBList ecbls ** P ->
   s |= EvtInv_part1 ecbls tcbls ** P.
Proof.
unfold EvtInv_part1.
intros.
sep pauto; eauto.
Qed.

Lemma fold_EvtInv_part2:
forall s P ecbls tcblh tcbvl vhold fecbh eventl evatoms evstructs evarrays
      sinfol scapl minfol mcapl qattrl qcapl semeibs muxeibs qeibs pbls ebls locmp ptrmp,
   R_Q_Data_P evstructs evarrays ->
   vhold = vhold_addr ->
   SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs ->
   MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs ->
   Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs ->
   evcre_nodup locmp ptrmp ->
   evdel_nodup locmp ptrmp ->
   eibref_distinct semeibs muxeibs qeibs ->
   s |= AOSEventFreeList fecbh eventl **
          Hebls ebls ** AErrblkList ebls **
          Hpbls pbls ** APosblkList pbls **
          HEvAtomHeap evatoms **  AEvAtomHeap evatoms **
          HEvStructHeap evstructs **  AEvStructHeap evstructs **
          HEvArrayHeap evarrays **  AEvArrayHeap evarrays **
          HSEMInfo semeibs ** ASemEIBs sinfol scapl semeibs ecbls vhold ** 
          HMuxInfo muxeibs ** AMuxEIBs minfol mcapl muxeibs ecbls vhold **
          HQAttr qeibs ** AMqEIBs qattrl qcapl qeibs ecbls vhold **
          HEvLoc locmp ** HEvPtr ptrmp ** 
          tcbllsegevaux tcblh tcbvl locmp ptrmp** P ->
   s |= EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl ** P.
Proof.
unfold EvtInv_part2.
intros.
sep pauto; eauto.
Qed.

Lemma unfold_EvtInv_frm:
forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl P,
    EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl ** P ==>
    EvtInv_part1 ecbls tcbls ** EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl ** P.
Proof.
unfold EvtInv.
unfold EvtInv_part1.
unfold EvtInv_part2.
intros.
sep auto.
Qed.

Lemma fold_EvtInv_frm:
forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl P,
    EvtInv_part1 ecbls tcbls ** EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl ** P
    ==> EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl ** P.
Proof.
unfold EvtInv.
unfold EvtInv_part1.
unfold EvtInv_part2.
intros.
sep auto.
Qed.

Lemma fold_EvtInv_frm':
forall P ecbls tcblh tcbvl tcbls vhold ectrl osql qblkl msgql scapl mcapl qcapl,
    AOSQFreeList osql ** 
    AOSQFreeBlk qblkl **
    AECBList ectrl msgql ecbls  tcbls **
    HECBList ecbls ** EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl ** P
    ==> EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl ** P.
Proof.
unfold EvtInv.
unfold EvtInv_part2.
intros.
sep auto.
Qed.

Lemma can_change_aop_EvtInv_part1:
  forall ecbls tcbls,
    can_change_aop (EvtInv_part1 ecbls tcbls). 
Proof.
  intros.
  unfold EvtInv_part1.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_EvtInv_part1: can_change_aop.

Lemma can_change_aop_EvtInv_part2:
  forall ecbls tcblh tcbvl vhold scapl mcapl qcapl,
    can_change_aop (EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl). 
Proof.
  intros.
  unfold EvtInv_part2.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_EvtInv_part2: can_change_aop.

Lemma good_frm_EvtInv_part1: forall  ecbls tcbls,
    GoodFrm (EvtInv_part1 ecbls tcbls).
Proof.
  intros.
  unfold EvtInv_part1.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_EvtInv_part1  : good_frm_lemmas.

Lemma good_frm_EvtInv_part2: forall  ecbls tcblh tcbvl vhold scapl mcapl qcapl,
    GoodFrm (EvtInv_part2 ecbls tcblh tcbvl vhold scapl mcapl qcapl).
Proof.
  intros.
  unfold EvtInv_part2.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_EvtInv_part2  : good_frm_lemmas.

Lemma evtinv_part2_set_tcbvl_mid_preserve:
  forall v rtbl tcbls vll1 vll2 els vhold tcblh scapl mcapl qcapl
         vnxt vprev veptr vmsg vdly vstat vprio vx vy vbx vby
         vprev' veptr' vmsg' vdly' vstat' vprio' vx' vy' vbx' vby'
         s P,  
    TCBList_P v
              (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2))
              rtbl tcbls -> 
    s |= EvtInv_part2  els tcblh (vll1 ++ ((vnxt :: vprev :: veptr :: vmsg :: vdly :: vstat :: vprio :: vx :: vy :: vbx :: vby) :: vll2)) vhold scapl mcapl qcapl
             ** P ->
    s |= EvtInv_part2 els tcblh (vll1 ++ ((vnxt :: vprev' :: veptr' :: vmsg' :: vdly' :: vstat' :: vprio' :: vx' :: vy' :: vbx' :: vby') :: vll2)) vhold scapl mcapl qcapl
            ** P.  
Proof.
  introv Htlp Hsat.
  unfold EvtInv_part2 in *.
  sep pauto; eauto.
  trycancel_EvtInv.
  apply seplog_lemmas.astar_r_aemp_elim. 
  eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto. 
  sep cancel tcbllsegevaux.
  auto.
  eapply tcb_linked_list_same_next_mid; eauto. 
Qed.

Lemma evtinv_part2_set_node : 
  forall vltcb vltcb' p s P head vl vl' els vhold scapl mcapl qcapl,
    s |= EvtInv_part2  els head vltcb vhold scapl mcapl qcapl ** P -> 
    tcblist_get p head vltcb = Some vl -> 
    set_node p vl' head vltcb = vltcb' -> 
    same_prev_next vl vl' -> 
    s |= EvtInv_part2 els head vltcb' vhold scapl mcapl qcapl ** P. 
Proof.
   unfold EvtInv_part2.
   intros.
   sep pauto; eauto.
   unfold tcbllsegevaux in *.
   sep lift 5%nat.
   sep lift 5%nat in H.
   eapply llsegevaux_set_node; eauto.
Qed.

