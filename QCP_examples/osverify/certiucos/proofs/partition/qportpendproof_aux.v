Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.
Require Import OSTimeDlyPure.
Require Import OSTimeTickPure.
Require Import gjb_common.
Require Import corecommu_tactics.
Require Import sem_corecommu.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_symrules.
Require Import partition_absrules.
Require Import partition_taskeventrules.
Require Import partition_tactics.
Require Import partinv_lemmas.

Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma qportpend_nilblock_part1 : forall 
  r ri aop ls  (p':asrt ) (ct: tid) ier ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) vhold 
  scapl mcapl qcapl
  ptls dportls pri st m sus p_v tm_v msg_p t_opt wt pd pid nextdstp pst pintick poutick sz,
  symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
  can_change_aop p' -> GoodFrm p' ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  get tcbls ct = Some (pri,st,m,sus) ->
  get ecbls p_v = Some (absport, wt) ->
  get dportls p_v = Some (Z.to_nat DNUM, pd, pid, DestinationP nextdstp, pst, pintick, poutick, QueuePort sz nil) ->
  Int.unsigned tm_v <= 65535 ->
  ((t_opt = Some tm_v /\ tm_v <> Int.zero) \/ (t_opt = None /\ tm_v = Int.zero)) ->
  {| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct
  {{  <|| qportpend_idle_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil |) ?? qportpend_not_ready_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil |) ?? 
          qportpend_block (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil |) ;; aop ||>  **
  AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls  **
  AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
  AOSRdyTblGrp rtbl rgrp **
  EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList tcbls **
  HCurTCB ct **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier ier **
  A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv ct init_lg **
  A_dom_lenv ls ** p' }} 
  OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat |ₑ ′ OS_STAT_PORT
  {{ EX v' v'1 v'2 v'0 v'3 v'4,  
  [| ct = (v'4, Int.zero)  /\ p1 <> Vnull /\ join v'1 v'2 tcbls /\ TCBList_P p1 tcbl1 rtbl v'1 /\ 
     TCBList_P (Vptr ct) (tcbcur :: tcbl2) rtbl v'2 /\ 
     struct_type_vallist_match OS_TCB_flag tcbcur /\ 
     V_OSTCBPrev tcbcur = Some v' /\ V_OSTCBNext tcbcur = Some v'3  |] **
  <||
  qportpend_idle_err
  (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
  ?? qportpend_not_ready_err
      (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
      ?? qportpend_block
        (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; aop ||>  **
  A_dom_lenv ls **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'4, Int.zero) **
  Astruct (v'4, Int.zero) OS_TCB_flag (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT))))) **
  dllseg v'3 (Vptr (v'4, Int.zero)) v'0 Vnull tcbl2 OS_TCB_flag V_OSTCBPrev
    V_OSTCBNext **
  GV OSTCBList @ OS_TCB ∗ |-> p1 **
  tcbdllseg p1 Vnull v' (Vptr (v'4, Int.zero)) tcbl1 **
  AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
  AOSRdyTblGrp rtbl rgrp **
  EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl**
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList tcbls **
  HCurTCB (v'4, Int.zero) **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr ** Aier ier ** 
  A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv (v'4, Int.zero) init_lg ** p'}} .
Proof.
  intros * H H0 Hfrm. intros.
  unfold AOSTCBList at 1.
  naive pure intro.
  unfold tcbdllseg at 2.
  cbn [dllseg].
  unfold node.
  naive pure intro.
  destruct H11.
  inverts H11.
  hoare name lift Astruct pre.
  hoare name lift (Agvarmapsto OSTCBCur) pre.
  hoare name lift A_dom_lenv pre.
  hoare name lift Aop pre.
  apply struct_type_vallist_match_os_tcb_flag in H15 as ?.
  do 11 destruct H11.
  (* OSTCBCur ′ → OSTCBStat =ₑ OSTCBCur ′ → OSTCBStat ||ₑ ′ OS_STAT_PORT;ₛ *)
  eapply forward_rule2.
  { eapply assign_rule_struct_g_aop_typeneq with (tp1 :=  OS_TCB_flag) (ls:= ls) (vl:= tcbcur);
  [  intro s; split;intros Hs;exact Hs
  | simpl; auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse | 
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ] .
  intros.
  eapply symbolic_lemmas.bop_rv.
  2: symbolic_execution.
  unfold OS_TCB, OS_TCB_flag in *.
  eapply symbolic_lemmas.struct_member_rv_g_typeneq ;eauto.
  cbn. eauto.
  all: go.
  subst tcbcur. simpl. lia. 
  subst tcbcur. destruct H15 as [_ [_ [_ [ _ [_ [? _]]]]]]. destruct x4;tryfalse. unfold or. destruct (Int.ltu Int.zero i || Int.ltu Int.zero ($ OS_STAT_PORT));auto.
  subst tcbcur. simpl. lia.  }
  subst tcbcur.
  cbn [update_nth_val nth_val'].
  remember ( (x
  :: x0
     :: x1
        :: x2
           :: x3
              :: match or x4 (V$ OS_STAT_PORT) with
                 | Some v'5 => v'5
                 | None => Vundef
                 end :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)) as tcbcur.
  intros.
  exists v' v'1 v'2 v'0 v'3 v'4.
  sep autocancel.
  sep pauto.
  inverts H17.
  sep pauto.
  inverts H17. auto.
  inverts H17.
  splits;auto.
Qed.


Lemma qportpend_nilblock_part2: forall 
r ri aop ls  (p':asrt ) (ct: tid) ier ptbl p1 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) vhold 
scapl mcapl qcapl ptls dportls
pri st m sus p_v tm_v msg_p t_opt wt pd pid nextdstp pst pintick poutick sz v' v'1 v'2 v'0 v'3 v'4,
symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
can_change_aop p' -> GoodFrm p' ->
RH_TCBList_ECBList_P ecbls tcbls ct ->
get tcbls ct = Some (pri,st,m,sus) ->
get ecbls p_v = Some (absport, wt) ->
get dportls p_v = Some (Z.to_nat DNUM, pd, pid, DestinationP nextdstp, pst, pintick, poutick, QueuePort sz nil) ->
Int.unsigned tm_v <= 65535 ->
((t_opt = Some tm_v /\ tm_v <> Int.zero) \/ (t_opt = None /\ tm_v = Int.zero)) -> 
(ct = (v'4, Int.zero)  /\ p1 <> Vnull /\ join v'1 v'2 tcbls /\ TCBList_P p1 tcbl1 rtbl v'1 /\ 
TCBList_P (Vptr ct) (tcbcur :: tcbl2) rtbl v'2 /\ 
struct_type_vallist_match OS_TCB_flag tcbcur /\ 
V_OSTCBPrev tcbcur = Some v' /\ V_OSTCBNext tcbcur = Some v'3 ) ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <||
  qportpend_idle_err
  (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
  ?? qportpend_not_ready_err
      (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
      ?? qportpend_block
        (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; aop ||>  **
  A_dom_lenv ls **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
  Astruct ct OS_TCB_flag (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT))))) **
  dllseg v'3 (Vptr ct) v'0 Vnull tcbl2 OS_TCB_flag
    V_OSTCBPrev V_OSTCBNext **
  GV OSTCBList @ OS_TCB ∗ |-> p1 **
  tcbdllseg p1 Vnull v' (Vptr ct) tcbl1 **
  AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
  AOSRdyTblGrp rtbl rgrp **
  EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList tcbls **
  HCurTCB ct **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier ier ** 
  A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv ct init_lg ** p'}} OSTCBCur ′ → OSTCBDly =ₑ timeout ′ 
  {{ <||
  qportpend_idle_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
  ?? qportpend_not_ready_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
     ?? qportpend_block (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; aop ||>  **
  A_dom_lenv ls **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'4, Int.zero) **
  Astruct (v'4, Int.zero) OS_TCB_flag (update_nth_val 4 (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT))))) (Vint32 tm_v)) **
  dllseg v'3 (Vptr (v'4, Int.zero)) v'0 Vnull tcbl2 OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
  GV OSTCBList @ OS_TCB ∗ |-> p1 **
  tcbdllseg p1 Vnull v' (Vptr (v'4, Int.zero)) tcbl1 **
  AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
  AOSRdyTblGrp rtbl rgrp **
  EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList tcbls **
  HCurTCB (v'4, Int.zero) **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) ** Aisr empisr ** Aier ier ** 
  A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv (v'4, Int.zero) init_lg ** p'}}.
Proof.
  intros.
  simpljoin1.
  apply struct_type_vallist_match_os_tcb_flag in H13 as ?.
  simpljoin1.
  cbn [update_nth_val nth_val'].
  remember ( (x
  :: x0
     :: x1
        :: x2
           :: x3
              :: val_inj (or x4 (V$ OS_STAT_PORT))
                 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)) as tcbcur.
  (* OSTCBCur ′ → OSTCBDly =ₑ timeout ′;ₛ *)
  eapply forward_rule2.
  { eapply assign_rule_struct_g_aop_typeneq with (tp1 :=  OS_TCB_flag) (ls:= ls) (vl:= tcbcur);
  [  intro s; split;intros Hs;exact Hs
  | simpl; auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic_execution
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ] .
  pauto. subst tcbcur;simpl;lia. }
  intros.
  subst tcbcur.
  cbn [update_nth_val nth_val'].
  sep autocancel.
Qed.

Lemma qportpend_nilblock_part3: forall 
r ri aop ls  (p':asrt ) (ct: tid) ier ptbl p1 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) vhold 
scapl mcapl qcapl ptls dportls
pri st m sus p_v tm_v msg_p t_opt wt pd pid nextdstp pst pintick poutick sz v' v'1 v'2 v'0 v'3 v'4,
symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
can_change_aop p' -> GoodFrm p' ->
RH_TCBList_ECBList_P ecbls tcbls ct ->
get tcbls ct = Some (pri,st,m,sus) ->
get ecbls p_v = Some (absport, wt) ->
get dportls p_v = Some (Z.to_nat DNUM, pd, pid, DestinationP nextdstp, pst, pintick, poutick, QueuePort sz nil) ->
Int.unsigned tm_v <= 65535 ->
((t_opt = Some tm_v /\ tm_v <> Int.zero) \/ (t_opt = None /\ tm_v = Int.zero)) -> 
(ct = (v'4, Int.zero)  /\ p1 <> Vnull /\ join v'1 v'2 tcbls /\ TCBList_P p1 tcbl1 rtbl v'1 /\ 
TCBList_P (Vptr ct) (tcbcur :: tcbl2) rtbl v'2 /\ 
struct_type_vallist_match OS_TCB_flag tcbcur /\ 
V_OSTCBPrev tcbcur = Some v' /\ V_OSTCBNext tcbcur = Some v'3 ) ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
  {{ <||
  qportpend_idle_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
  ?? qportpend_not_ready_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)
     ?? qportpend_block (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; aop ||>  **
  A_dom_lenv ls **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'4, Int.zero) **
  Astruct (v'4, Int.zero) OS_TCB_flag (update_nth_val 4 (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT))))) (Vint32 tm_v)) **
  dllseg v'3 (Vptr (v'4, Int.zero)) v'0 Vnull tcbl2 OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
  GV OSTCBList @ OS_TCB ∗ |-> p1 **
  tcbdllseg p1 Vnull v' (Vptr (v'4, Int.zero)) tcbl1 **
  AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
  AOSRdyTblGrp rtbl rgrp **
  EvtInv ecbls p1
    (tcbl1 ++ tcbcur :: tcbl2) tcbls
    vhold scapl mcapl qcapl **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList tcbls **
  HCurTCB (v'4, Int.zero) **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) ** Aisr empisr ** Aier ier ** A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv (v'4, Int.zero) init_lg ** p'}}
  OS_EventTaskWait (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­)
  {{ EX ier' rgrp' tcbcur' y bitx bity ry rtbl', [| (st = rdy /\ sus = false) |] **
  [|  tcbcur' = update_nth_val 2 (update_nth_val 4 (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT)))) ) (Vint32 tm_v)) (Vptr p_v) /\ 
      V_OSTCBY tcbcur = Some (Vint32 y) /\ 
      V_OSTCBBitX tcbcur = Some (Vint32 bitx) /\
      V_OSTCBBitY tcbcur = Some (Vint32 bity) |] **    
  [| nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) /\
      rtbl' = update_nth_val (nat_of_Z (Int.unsigned y)) rtbl (Vint32 (Int.and ry (Int.not bitx))) |] ** 
  [| RH_TCBList_ECBList_P (set ecbls p_v (absport, (ct :: wt))) (set tcbls ct (pri, wait (os_stat_port p_v) t_opt, m,sus)) ct|] **
 <|| aop ||>   **
  AOSTCBList p1 (Vptr (v'4, Int.zero) ) tcbl1 (tcbcur' :: tcbl2) rtbl' ct 
   (set tcbls ct (pri, wait (os_stat_port p_v) t_opt, m,sus))  ** 
  AOSTCBPrioTbl ptbl rtbl' (set tcbls ct (pri, wait (os_stat_port p_v) t_opt, m,sus)) ptls vhold ** 
  AOSRdyTblGrp rtbl' rgrp' **
  EvtInv (set ecbls p_v (absport, (ct :: wt))) p1 (tcbl1++(tcbcur'::tcbl2)) (set tcbls ct (pri, wait (os_stat_port p_v) t_opt, m,sus)) vhold scapl mcapl qcapl **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  HTCBList (set tcbls ct (pri, wait (os_stat_port p_v) t_opt, m,sus)) **
  HCurTCB ct **
  Hdomainportl dportls **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier ier' ** A_isr_is_prop **
  aemp_isr_is **
  p_local OSLInv ct init_lg **
  A_dom_lenv ls ** p' }}.
Proof.
  intros.
  simpljoin1.
  apply struct_type_vallist_match_os_tcb_flag in H13 as ?.
  simpljoin1.
  cbn [update_nth_val nth_val'].
  remember ((x
  :: x0
     :: x1
        :: x2
           :: Vint32 tm_v
              :: val_inj (or x4 (V$ OS_STAT_PORT)) :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)) as tcbcur.
  unfold EvtInv at 1.
  hoare normal pre. naive pure intro.
  (* qportpend_idle_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) *)
  destruct (Int.eq pri  (Int.repr OS_IDLE_PRIO)) eqn:?. 
  { apply Int_eq_dec in Heqb.
    subst pri.
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | |  ].
    eapply qportpend_idle_err_abt;eauto. can_change_aop_solver.
    eapply absabort_rule. } 
  (* qportpend_not_ready_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) *)
  assert ((~ (st = rdy /\ sus = false)) \/ (st = rdy /\ sus = false)) as [ | Hst ] by tauto.
  { hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | |  ].
    eapply qportpend_not_ready_err_abt;eauto. can_change_aop_solver.
    eapply absabort_rule. } 
  (* qportpend_block (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) *)
  hoare name lift osdomainportid pre.
  hoare name lift curtid pre.
  hoare name lift absecblsid pre.
  hoare name lift abstcblsid pre.
  hoare name lift Aop pre.
  eapply abscsq_rule';[apply noabs_oslinv | |  ].
  eapply qportpend_block_cont;eauto. can_change_aop_solver. 
  (* OS_EventTaskWait (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­) *)
  hoare name lift AECBList pre.
  rename v'7 into ectrl. rename v'10 into msgql.
  unfold AECBList.
  naive pure intro.
  rename v'7 into headptr. rename H23 into Hecbl.
  hoare_assert_pure (isptr p1).
  { sep name lift (tcbdllseg p1) in H23.
    unfold tcbdllseg in H23. 
    eapply oscore_common.dllseg_head_isptr' in H23.
    auto. } 
  naive pure intro.
  destruct H23 as [ | (p1_v & Hptr)];[subst;tryfalse | subst ].
  hoare name lift AOSRdyTblGrp pre.
  hoare_assert_pure (RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl (Int.repr OS_IDLE_PRIO) rtbl /\ array_type_vallist_match Tint8 rtbl /\ length rtbl = (nat_of_Z OS_RDY_TBL_SIZE)).
  { unfold AOSRdyTblGrp, AOSRdyTbl in H16.
    sep normal in H16. sep split in H16. tauto. }
  naive pure intro.
  destruct H16 as [Hlgrp [Hidelpri [Htyperltbl Hlenrtbl]]].
  assert (exists et etbl petbl, get_ectr (Vptr p_v) headptr ectrl = Some (et,etbl, petbl)) as (et & etbl & petbl & Fget_ectr).
  { eapply ECBList_P_get_ectr_some in Hecbl; try eauto. }
  hoare name lift evsllseg pre.
  eapply backward_rule1.
  { intros s Hs. eapply get_ectr_decompose in Hs;eauto. }
  naive pure intro.
  rename v'7 into et_next. rename v'10 into ectrl1. rename v'24 into ectrl2.
  rename v'25 into msgql1. rename v'26 into msgql2. rename v'27 into portmsgq.
  destruct H16 as (Hetnext & ? &  ? & Hgetectr1 & Hgetectr2 & Hheadptr & Hnexptr ). subst.
  hoare_assert_pure (length ectrl1 = length msgql1).
  { sep name lift evsllseg in H16.
    eapply evsllseg_list_len_eq;eauto. }
  naive pure intro. rename H16 into Hleneq.
  hoare_assert_pure (V_OSEventType et = Some (V$ OS_EVENT_TYPE_PORT)).
  { sep name lift AEventNode in H16.
    eapply ecblist_p_decompose_new in Hecbl;eauto.
    destruct Hecbl as [ecbls1 [ecbls2 [Hecbl1 [Hecbl2  [Hjoinecb Hgetlast]]]]].
    cbn in Hecbl2. destruct Hecbl2 as (? & ? & ? & ? & (? & ? & ? & ? & (? & ? & ? ))).
    inverts H23.
    assert (x11 = (absport, wt)).
    { eapply join_sig_get in H27;eauto.
      eapply EcbMod.join_get_get_r in Hjoinecb;eauto.
      unfold get, EcbMap in H4.
      rewrite H4 in Hjoinecb. inverts Hjoinecb. auto. }
    subst.  
    unfold RLH_ECBData_P in H28. destruct portmsgq;tryfalse.
    unfold AEventNode, AEventData in H16.
    sep split in H16. auto. }
  naive pure intro. rename H16 into Heventtype.
  assert (Int.unsigned pri < 64 /\  x5 = Vint32 pri /\ x7 = Vint32 (pri >>ᵢ $ 3) /\ x8 = Vint32 ($ 1<<ᵢ (pri&ᵢ$ 7)) /\ x9 = Vint32 (Int.shl ($ 1) (pri >>ᵢ $ 3))) as (Hran & ? & ? & ? & ?).
  { cbn in H12. simpljoin1.  inverts H12. inverts H24.
    unfold TCBNode_P, V_OSTCBPrio in *.
    assert (x13 = (pri, rdy, m, false)).
    {  assert ((@get tid (prod (prod (prod priority taskstatus) msg) susstatus)
    TcbMod.map TcbMap tcbls (@pair block Int.int v'4 Int.zero)) = Some x13).
       eapply join_get_r;eauto.
       eapply join_sig_get;eauto.
       clear -H12 H3. unfold susstatus in *.
       rewrite H12 in H3. inverts H3. auto. }
    subst x13. clear-  H26.
      cbn in *. simpljoin1. unfold RL_TCBblk_P in H1. simpljoin1.
      cbn in *.  inverts H0. inverts H1. inverts H3. inverts H4. inverts H5. inverts H6. auto. }
  subst.
  eapply forward_rule2.
  eapply call_rule';[
      cbn;unfold OS_EventTaskWait_spec;eauto | idtac .. ].
  { unfold AEventNode, AOSEvent, node.  intros s Hs. sep normal in Hs. sep destruct Hs.
    eapply rvl_elim;[ | eapply rvl_nil]. 
    sep_get_rv.  }
  { (* ==> pre*)
    intros s Hs;unfold_spec.  unfold node.
    sep name lift A_isr_is_prop in Hs. sep name lift Ais in Hs.  
    sep name lift Aisr in Hs. 
    eapply elim_a_isr_is_prop in Hs.
    sep name lift aemp_isr_is in Hs. sep name lift Ais in Hs.  
    sep name lift Aisr in Hs. 
    eapply elim_aemp_isr_is_prop in Hs.
    sep normal. sep eexists. sep autocancel.
    cbn in H12.  destruct H12 as [? [? [? [? [? [? ?]]]]]].
    simpljoin1. inverts e. inverts e0.
    unfold TCBNode_P, V_OSTCBPrio in *.
    assert (x9 = (pri, rdy, m, false)).
    {  assert ((@get tid (prod (prod (prod priority taskstatus) msg) susstatus)
    TcbMod.map TcbMap tcbls (@pair block Int.int v'4 Int.zero)) = Some x9).
       eapply join_get_r;eauto.
       eapply join_sig_get;eauto.
       clear -H12 H3. unfold susstatus in *.
       rewrite H12 in H3. inverts H3. auto. }
    subst x9.
    destruct t as [? [? [? ?]]].
    cbn [nth_val] in *. 
    unfold RL_TCBblk_P, R_TCB_Status_P, RHL_RdyI_P, V_OSTCBPrio, V_OSTCBX, V_OSTCBY, V_OSTCBBitX, V_OSTCBBitY, V_OSTCBStat, V_OSTCBEventPtr in *. 
    cbn [nth_val] in *. destruct H23 as [prio [x [y [bitx [bity [stat [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]]]].
    destruct H36 as [? [? ?]]. inverts H36. inverts H16. inverts H23. inverts H29.
    sep pauto;eauto.
    { specialize (H23 prio m (ltac:(reflexivity))) as [? [? ?]].
      inverts H36.
      do 6 eexists. splits;eauto. cbn. eauto. splits;auto.
    right;right;right;right;right;right;right;left. clear. unfold OS_STAT_RDY, OS_STAT_PORT. mauto.
    eexists. splits;eauto. }
    splits;auto. 
    specialize (H23 prio m (ltac:(reflexivity))) as [? [? ?]]. inverts H36.
    clear - H13 H6. 
    destruct H13 as [? h]. split;[auto | ].  do 4 (destruct h as [? h]; split;[cbn;pauto| ]). 
    destruct h as [? h]; split;[ | ]. 2: { do 5 (destruct h as [? h]; split;[cbn;auto| auto]). }
    unfold or. cbn in *. clear. unfold OS_STAT_RDY, OS_STAT_PORT. mauto. }
  { good_frm_sovler. }
  { sep_unfold_funpost. intros s Hs. sep destruct Hs. sep auto. }
  { sep_unfold_funpre. intros s Hs. sep destruct Hs. sep auto. }
  { simpl;eauto. }
  unfold getasrt; unfold OS_EventTaskWaitPost, OS_EventTaskWaitPost'.
  intros s Hs. unfold AOSTCBList,AOSTCBPrioTbl in *. 
  sep normal in Hs. sep destruct Hs. 
  sep name lift logic_lv in Hs.
  sep name lift (nth_val 0 (Vptr p_v :: nil)) in Hs.
  sep name lift (update_nth_val 2) in Hs.
  do 3 apply sep_pure_split in Hs as [? Hs].
  cbn in H23, H24. inversion H23.  subst x10. inversion H24.
  subst x8 x7 x11 x12 x13 x14 x26 x27. clear H23 H24.
  destruct H16 as [? [? [? [? [? [? [? [? [? ?] ]]]]]]]].
  subst x19.
  sep name lift R_PrioTbl_P in Hs.
  apply sep_pure_split in Hs as [Hpritbl Hs].
  sep normal. subst rgrp.
  exists x28 (Vint32 x17). eexists. 
  exists x20 x21 x22 x23 x16. 
  do 2 eexists. exists v'1. exists (set v'2 (v'4, Int.zero) (pri, wait (os_stat_port p_v) t_opt, m, sus)) x29.
  sep lift 11%nat.
  apply astar_l_apure_intro.
  2:{ unfold V_OSTCBBitX, V_OSTCBBitY, V_OSTCBY in *. cbn [nth_val] in *.   splits;eauto.  }
  sep name lift Aier in Hs. sep name lift Ais in Hs. sep name lift Aisr in Hs.
  eapply add_aemp_isr_is_prop in Hs;eauto.
  sep name lift Aier in Hs. sep name lift Ais in Hs. sep name lift Aisr in Hs.
  eapply add_a_isr_is_prop in Hs;eauto.
  sep autocancel.
  sep split in Hs.
  cbn [nth_val]. 
  unfold tcbdllseg.
  cbn [dllseg].  
  unfold V_OSTCBPrev, V_OSTCBNext in H14, H15; cbn in H14, H15. inverts H14. inverts H15.
  destruct H12 as [? [? [? [? [H12_ [H12_0 [H12_1  [Htcbnode H12]]]]]]]]. 
  inverts H12_. cbn in H12_0. inverts H12_0.
  destruct Hst as [? ?];subst st sus.
  assert (x8 = (pri, rdy, m, false)).
  {  assert ((@get tid (prod (prod (prod priority taskstatus) msg) susstatus)
  TcbMod.map TcbMap tcbls (@pair block Int.int v'4 Int.zero)) = Some x8).
  eapply join_get_r;eauto.
  eapply join_sig_get;eauto.
  clear - H14 H3. unfold susstatus in *.
  rewrite H14 in H3. inverts H3. auto. } 
  subst x8. subst x15.
  sep normal. sep eexists.
  unfold V_OSTCBNext at 1, V_OSTCBPrev at 1. cbn [nth_val].
  cbn [update_nth_val] in Hs.
  unfold val_inj at 1. 
  sep autocancel.
  sep cancel dllseg.
  sep split;eauto. 
  7:{ (* join v'1 *)
      eapply join_set_r;eauto. unfold indom.
      eexists. eapply join_sig_get;eauto. }
  { unfold EvtInv, AECBList. sep normal. sep eexists. sep autocancel.
    sep name lift (evsllseg et_next) in Hs. sep name lift AEventNode in Hs.
    eapply evsllseg_add_head in Hs;eauto.
    sep name lift (evsllseg headptr) in Hs.
    eapply ucos_common.evsllseg_app in Hs;eauto.
    sep autocancel.
    2: { subst x18. unfold V_OSEventListPtr in *. erewrite nth_upd_neqrev;eauto. }
    instantiate (1:= v'16). instantiate (1:= v'15). instantiate (1:= v'14).
    sep split;auto.
    eapply ASemEIBs_port_set_ecbls_preserve;eauto.
    sep cancel ASemEIBs.
    eapply AMuxEIBs_port_set_ecbls_preserve;eauto.
    sep cancel AMuxEIBs.
    eapply AMqEIBs_port_set_ecbls_preserve;eauto.
    sep name lift tcbllsegevaux.
    sep name lift tcbllsegevaux in Hs.
    eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve;eauto.
    eapply tcb_linked_list_same_next_split.
    eapply tcb_linked_list_same_next_self;eauto.
    cbn. split;auto. eapply tcb_linked_list_same_next_self;eauto.
    { (* Q_ECB_P *)
      eapply mq_ecb_p_sem_set_ecbls_port_preserve;eauto. }
    { (* MUX_ECB_P *)
      eapply mux_ecb_p_port_set_preserve;eauto. }
    { (* SEM_ECB_P *)
      eapply sem_ecb_p_mutex_set_preserve;eauto. }
    clear s Hs.
    eapply  ecblist_p_decompose_new in Hecbl;[ | eauto.. ].
    simpljoin1.
    cbn in H15.
    simpljoin1. inversion H15;subst x10. clear H15.
    assert (x11 = (absport, wt)).
    { eapply join_sig_get in H34;eauto.
      eapply EcbMod.join_get_get_r in H16;eauto.
      unfold get,EcbMap in H4.
      rewrite H4 in H16. inverts H16. auto. }
    eapply ecblist_p_compose with (mqls2 := (set x8 p_v (absport, (v'4, Int.zero) :: wt))) (q:= (Vptr p_v)).
    { unfold set, EcbMap.
      eapply EcbMod.join_set_r;eauto.
      unfold EcbMod.indom.
      eapply join_sig_get in H34;eauto. }
    { eapply ECBList_P_high_tcb_block_hold_port;eauto.
      eapply joinsig_join_getnone;eauto. }
    cbn. cbn in *. inverts H23. inverts H24. inverts H25.
    eexists. splits;eauto.
    { (* R_ECB_ETbl_P *) 
      eapply R_ECB_ETbl_P_high_tcb_block_hold_port;eauto. }
    { (* R_ECB_PETbl_P *) 
      eapply R_ECB_PETbl_P_high_tcb_block_hold';eauto.
      rewrite  Heventtype. clear. mauto.
      unfolds V_OSEventType. unfold not. intros. erewrite nth_upd_neqrev in H23 by eauto. clear - H23. tryfalse.
      unfold not. intros [? [? ?]]. tryfalse.
    }
    subst x11.
    exists (absport, (v'4, Int.zero) :: wt).
    do 2 eexists.
    splits;eauto.
    unfolds V_OSEventListPtr. erewrite nth_upd_neqrev;eauto.
    eapply join_sig_set;eauto. 
    eapply ECBList_P_high_tcb_block_hold_port;eauto.
    eapply joinsig_get_none;eauto.
    }
  { (* R_PrioTbl_P *) 
    eapply R_PrioTbl_P_hold1;eauto.
  }
  { (* RL_RTbl_PrioTbl_P *) clear Hs. 
    subst x16. unfold TCBNode_P, RL_TCBblk_P, V_OSTCBPrio in *. simpljoin1.
    cbn in *. 
    repeat match goal with | H: Some _ = Some _ |- _ => inverts H end. 
    eapply RL_RTbl_PrioTbl_P_update_rtbl;eauto. }    
  { (* RH_TCBList_ECBList_P *)
    eapply RH_TCBList_ECBList_P_update_rdy2port;eauto. }
  { (* TCBList_P (Vptr (v'4, Int.zero)) ..  x20 (set v'2 (v'4, Int.zero) (pri, wait (os_stat_port p_v) t_opt, m, false))  *)
    subst.
    clear Hs.
    remember  (x0 :: v' :: x1 :: x2 :: x3 :: x4
                    :: Vint32 pri :: x6 :: Vint32 (pri >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(pri&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(pri >>ᵢ $ 3)) :: nil) as tcbcur.
    assert (TCBNode_P (update_nth_val 2 (update_nth_val 4 (update_nth_val 5 tcbcur (val_inj (or (nth_val' 5 tcbcur) (Vint32 ($ OS_STAT_PORT)))) ) (Vint32 tm_v)) (Vptr p_v))
    (update_nth_val ∘ (Int.unsigned x20) rtbl (Vint32 (x23 &ᵢInt.not x21))) 
    (pri, wait (os_stat_port p_v) t_opt, m, false)).
    { eapply TCBNode_P_update_rdy2port;eauto.
      subst. clear - H24. cbn in *. auto.
      subst. clear - H23. cbn in *. auto.  }
    subst. cbn [update_nth_val nth_val'] in H14.
    cbn. 
    simpljoin1.
    exists (v'4, Int.zero) x0 x7 (pri, wait (os_stat_port p_v) t_opt, m, false).
    splits;auto.
    - eapply join_sig_set;eauto.
    - cbn in H14. simpljoin1. inverts H14.  unfold RL_TCBblk_P, V_OSTCBPrio, V_OSTCBBitX, V_OSTCBY in *. 
      simpljoin1. cbn [nth_val] in *. inverts H14. inverts H24. inverts H23.
      eapply update_rtbl_tcblist_hold;eauto.
      eapply R_PrioTbl_P_impl_prio_neq_cur in Hpritbl;eauto.
      intros.
      lets Has : tcbjoin_get_getneq H12_1 H14.
      destruct Has.
      eapply Hpritbl; eauto.
      eapply join_get_r in H10;eauto.
  }
  { (* TCBList_P p1 tcbl1 x20 v'1*) 
    subst x16. clear Hs.
    cbn in Htcbnode. unfold RL_TCBblk_P, V_OSTCBPrio, V_OSTCBBitX, V_OSTCBY in *. 
    simpljoin1. cbn [nth_val] in *. 
    inverts H16. inverts H24. inverts H23.
    eapply update_rtbl_tcblist_hold;eauto.
    eapply R_PrioTbl_P_impl_prio_neq_cur with (curtid := (v'4, Int.zero)) (curprio := x) in Hpritbl ;eauto.
    unfolds in Hpritbl.
    intros.
    lets Has: tcbjoin_join_get_neq  H12_1 H10 H15.
    destruct Has.
    eapply Hpritbl; eauto.
  }
Qed.

Lemma ptrconst_rv: 
  forall (s : RstateOP) a, s |= Rv eptrconst a @ (Tptr Tint32) == Vptr a.
Proof.
  intros.
  simpl.
  destruct s as [[[[[[[]]]]]]].
  simpl.
  splits; auto.
Qed.


Lemma qportpend_nilblock_finalcriticalregion:  forall  (msg_p: addrval) (tm_v: int32) errv dkp_v p_v (kp_b cha_b: block) vsem  (csem: channel_semaphore) resn
(ct: block * int32) (ier: ier),
Int.unsigned tm_v <= 65535 ->
OSPortAttrTblMode p_v = V$ QUEUE ->
OSPortAttrTblDir p_v = V$ DESTINATION ->
Int.unsigned ($ Z.of_nat csem) <= 255 ->
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv ct init_lg **
 ((EX v0 : val, LV msg_ptr @ OSMsg_t ∗ |-> v0) **
  (EX v0 : val, LV timeout @ Int16u |-> v0) **
  (EX v0 : val, LV port_ptr @ OS_Port ∗ |-> v0) **
  (EX v0 : val, LV kport @ OS_K_Port ∗ |-> v0) **
  (EX v0 : val, LV dstKPort @ OS_K_Port ∗ |-> v0) **
  (EX v0 : val, LV channel @ OS_Channel ∗ |-> v0) **
  (EX v0 : val, LV semaphore @ char_t |-> v0) **
  (EX v0 : val, LV resource_get_res @ char_t |-> v0) **
  (EX v0 : val, LV err @ char_t |-> v0) ** Aemp) **
 Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX ier0 : language.ier, Aier ier0)) **
A_dom_lenv
  ((msg_ptr, OSMsg_t ∗)
   :: (timeout, Int16u)
      :: (port_ptr, OS_Port ∗)
         :: (kport, OS_K_Port ∗)
            :: (dstKPort, OS_K_Port ∗)
               :: (channel, OS_Channel ∗)
                  :: (semaphore, char_t) :: (resource_get_res, char_t) :: (err, char_t) :: nil),
Afalse|}|- ct
{{Aie true **
  Ais nil **
  Acs nil **
  Aisr empisr **
  Aier ier **
   <||
  ASSERT (port_indomainport (Vptr p_v)) ;; qportpend_after_sched (|Vptr p_v::nil|);; (
    (spec_code_cons (portpend_accwithoutcheck (Vptr p_v :: Vptr msg_p :: vsem :: errv ::nil)) 
    (qportpend_block_get (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ;; END Some (errv)))
  ?? qportpend_block_timeout (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)) ||>  **
  p_local OSLInv ct
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  LV timeout @ Int16u |-> Vint32 tm_v **
  LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
  A_dom_lenv
    ((msg_ptr, OSMsg_t ∗)
     :: (timeout, Int16u)
        :: (port_ptr, OS_Port ∗)
           :: (kport, OS_K_Port ∗)
              :: (dstKPort, OS_K_Port ∗)
                 :: (channel, OS_Channel ∗)
                    :: (semaphore, char_t)
                       :: (resource_get_res, char_t) :: (err, char_t) :: nil) **
  LV resource_get_res @ char_t |-> (V$ resn) **
  LV semaphore @ char_t |-> (V$ Z.of_nat csem) **
  LV channel @ OS_Channel ∗ |-> Vptr (cha_b, Int.zero) **
  LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
  LV err @ char_t |-> Vint32 (Int.modu ($ OS_NO_ERR) ($ Byte.modulus)) **
  LV dstKPort @ OS_K_Port ∗ |-> dkp_v ** LV msg_ptr @ OSMsg_t ∗ |-> Vptr msg_p}} ENTER_CRITICAL;ₛ
If (OSTCBCur′→OSTCBMsg ==ₑ〈 Void ∗ 〉(eptrconst OS_PARTITION_MESSAGE_COME_ptr))
{err ′ =ᶠ OSPortAcceptWithoutCheck2 (·port_ptr ′, msg_ptr ′·);ₛ
OSTCBCur ′ → OSTCBMsg =ₑ 〈 (Void) ∗ 〉 NULL;ₛ
OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_RDY;ₛ
OSTCBCur ′ → OSTCBEventPtr =ₑ 〈 OS_EVENT ∗ 〉 NULL;ₛ
EXIT_CRITICAL;ₛ
RETURN err ′};ₛ
OS_EventTO (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­);ₛ
EXIT_CRITICAL;ₛ
RETURN 〈 char_t 〉 ′ OS_TIMEOUT {{Afalse}}.
Proof.
  intros * Htm Hmode Hdir Hcsem.
  (* ENTER_CRITICAL;ₛ *)
  partition_enter_trinv.
  naive pure intro.
  rename v' into ptbl. rename v'0 into p1. rename v'1 into p2. rename v'2 into tcbl1. rename v'3 into tcbcur.
  rename v'4 into tcbl2. rename v'5 into rtbl. rename v'6 into rgrp. rename v'8 into tcbls. rename v'9 into t.
  rename v'10 into vhold. rename v'11 into ptfree. rename v'12 into lfree. rename v'13 into ptls.
  rename v'14 into pattrb.  rename v'15 into acspace. 
  rename v'16 into  scapl. rename v'17 into mcapl. rename v'18 into qcapl.
  rename v'40 into cportlptr. rename v'41 into cportpl. 
  rename H into Htcbecb. rename H0 into Hcurtcb.
  rename H1 into Hjoindp. rename H2 into Hlpattr. rename H3 into Hinecb. rename H4 into Hlhdp.
  rename H5 into Hlhkp. rename H6 into Hlhchann. rename H7 into Hkpdp. rename H8 into Hkpchann. rename H9 into Hlhotherp. rename H10 into Hkpnodup.
  unfold AOSTCBList.
  naive pure intro.
  rename v' into tail1. rename v'0 into tail2. rename v'1 into tcbls1. rename v'2 into tcbls2.
  simpljoin1. rename H0 into Htcbjoin. rename H1 into Htcblp1. rename H2 into Htcblp2.
  unfold tcbdllseg at 2. cbn [dllseg].
  naive pure intro. rename v' into next_tcb. rename H0 into Htcbnext. rename H1 into Htcbpre. clear H2.
  (* If (OSTCBCur′→OSTCBMsg ==ₑ〈 Void ∗ 〉(eptrconst OS_PARTITION_MESSAGE_COME_ptr)) *)
  unfold node. naive pure intro. simpljoin1. inverts H0. rename v' into ct_b. rename H1 into Htype.
  apply struct_type_vallist_match_os_tcb_flag in Htype as ?. simpljoin1. 
  hoare normal pre. pure intro.
  eapply seq_rule.
  eapply ift_rule''. 
  { intros s Hs. 
    eapply symbolic_lemmas.bop_rv.
    symbolic_execution. auto.
    eapply symbolic_lemmas.cast_rv_tptr.
    eapply ptrconst_rv.
    cbn;auto.
    reflexivity.
    { clear Hs H0.
    do 4 destruct Htype as [? Htype]. clear - H3. destruct x2;tryfalse. destruct OS_PARTITION_MESSAGE_COME_ptr.  cbn;auto. destruct a,OS_PARTITION_MESSAGE_COME_ptr . cbn.  pauto.  }
    cbn. eauto. 
  }
  - (* branch : pend get *)
    instantiate (1:= Afalse). clear H0.
    naive pure intro.
    assert (x2 = Vptr OS_PARTITION_MESSAGE_COME_ptr) as Htcbmsg.
    { simpljoin1. destruct x2, OS_PARTITION_MESSAGE_COME_ptr;cbn in *;tryfalse. 
      clear - H0. destruct a. 
      assert (b0 = b \/ b0 <> b) as [ | ] by tauto.
      { subst.
      rewrite peq_true in H0.
      destruct (Int.eq i0 i) eqn:?; cbn in H0;tryfalse.
      apply Int_eq_dec in Heqb0. subst. auto. }
      rewrite peq_false in H0;auto.
      cbn in H0. tryfalse. }
    clear H0. subst x2.
    (* abs step *)
    destruct (get dportls p_v) as [port | ] eqn: Hdp.
    2: { partition_absrulestac port_indomainport_none_abt;apply absabort_rule. }
    destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
    assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
    2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
    subst pcn.
    hoare name lift AOSDomainPortPtrList pre.
    destruct Hinecb as [Hptrl Hinecb].
    eapply pptr_in_dportls1 in Hjoindp as ?;eauto.
    split_portlist. 
    rename H4 into Hdpnode. rename H5 into Hlendpl1. rename H6 into Hlendmsgl1. rename H3 into Hnprtl.
    destruct pdir.
    { exfalso. 
      eapply RL_PortAttr_dir_SOURCE in Hdpnode;eauto.
      rewrite Hdpnode in Hdir. clear - Hdir. mauto.
      rewrite nth_error_app2 by lia.
      rewrite Hlendpl1.
      rewrite Nat.sub_diag. simpl. auto. }
    destruct pt as [ ? | sz pq].
    { exfalso. 
      eapply RL_PortAttr_mode_SAMPLE in Hdpnode;eauto.
      rewrite Hdpnode in Hmode. clear - Hmode. mauto.
      rewrite nth_error_app2 by lia.
      rewrite Hlendpl1.
      rewrite Nat.sub_diag. simpl. auto. }
    partition_absrulestac port_indomainport_cont.
    unfold RH_CurTCB in Hcurtcb. destruct Hcurtcb as [curpri [st [m [sus Hcurtcb]]]].
    assert (exists wt, get ecbls p_v = Some (absport, wt)) as [wt Hportwt].
    { apply nth_error_split in Hnprtl as [? [? [? ?]]]. subst dpptrl.
      apply Forall_app in Hinecb as [? ?].
      inversion H3. auto. } 
    destruct Htcblp2 as [x [v' [tcbls2' [abstcb [? [? [Htcbsig [Htcbnode Htcblp2]]]]]]]].
    inverts H1. inverts H2. rename v' into next_tcb. 
    assert (abstcb = (curpri, st, m, sus)).
    { eapply join_sig_get in Htcbsig;eauto.
      eapply join_get_r in Htcbjoin;eauto. rewrite Htcbjoin in Hcurtcb. inverts Hcurtcb. auto. }
    subst abstcb.
    assert (m = Vptr OS_PARTITION_MESSAGE_COME_ptr).
    { unfold TCBNode_P in Htcbnode.
      simpljoin1.  clear - H1. unfold V_OSTCBMsg in H1. cbn in H1. inverts H1. auto. }
    subst m.
    (* qportpend_after_sched (|Vptr p_v :: nil|);; *)
    assert ( (st = rdy /\ (Vptr OS_PARTITION_MESSAGE_COME_ptr) = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port p_v) (Some Int.zero) /\ (Vptr OS_PARTITION_MESSAGE_COME_ptr) = Vnull /\ sus = false)\/ 
      (~ ((st = rdy /\ (Vptr OS_PARTITION_MESSAGE_COME_ptr) = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port p_v) (Some Int.zero) /\ (Vptr OS_PARTITION_MESSAGE_COME_ptr) = Vnull /\ sus = false))))  as [ Hst | Hst ] by tauto.
    2:{ hoare name lift curtid pre.
        hoare name lift abstcblsid pre.
        hoare name lift Aop pre.
        eapply abscsq_rule';[apply noabs_oslinv | | ].
        eapply qportpend_aftersch_abt;eauto.  
        can_change_aop_solver.
        apply absabort_rule. }
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | | ].
    eapply qportpend_aftersch_cont;eauto.  
    can_change_aop_solver.
    destruct Hst as [ [? [_ ?]] | [? [? ?]]];[subst | discriminate ].
    (* abs choice 1 *)
    hoare remember (1%nat::nil) pre.
    hoare abscsq;[ apply noabs_oslinv | auto ..  ].
    apply absinfer_choice1 with (q:= H1). 1,2: subst H1;go. sep auto.
    subst H1.
    (* err ′ =ᶠ OSPortAcceptWithoutCheck2 (·port_ptr ′, msg_ptr ′·);ₛ *)
    hoare name lift aemp_isr_is pre. hoare name lift Ais pre.  
    hoare name lift Aisr pre.
    eapply backward_rule1.
    { intros s Hs. 
      eapply elim_aemp_isr_is_prop in Hs. exact Hs. }
    eapply seq_rule.
    eapply calle_rule_lvar';[
      cbn;unfold OSPortAcceptWithoutCheck2_spec;eauto | 
      intros; do 5 try 
      (apply rvl_elim;[ symbolic_execution | ]);
      first [apply rvl_nil | simpl;auto] | 
       |
      idtac |
      idtac |
      simpl;eauto | 
      sep_unfold_funpost |
      sep_unfold_funpre 
      ].
    { (* ==> PRE *)
      intros s Hs. unfold_spec. unfold TmrInv in Hs.
      sep normal. sep eexists. sep autocancel.
      sep pauto;try eauto. 
    }
    { go. }
    { unfold retpost,OSPortAcceptWithoutCheck2Post, getasrt, OSPortAcceptWithoutCheck2Post'. 
      intros. sep destruct H1. sep split in H1. subst.  auto.  }
    { intros s Hs. eexists. sep auto. }
    { intros s Hs. eexists. sep auto. }
    unfold getasrt; unfold OSPortAcceptWithoutCheck2Post, OSPortAcceptWithoutCheck2Post'.
    naive pure intro.
    inversion H11. subst v'2 v'3. clear H11.
    inversion H12. subst v'0 v'1 v'4 v'5 v'6 v'7 v'9 v'13 v'10 v'12 v'14 v'15 v'16 v'17 v'18 v'19 v'21 v'23 v'24 v'25 v'26. 
    inversion H14. subst v'. clear H12 H14.
    rename v'8 into dport_new. rename v'11 into  msgl_new. rename v'20 into dportls1_new.
    rename v'22 into dportls_new. 
    (* OSTCBCur ′ → OSTCBMsg =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
    hoare name lift (Astruct (ct_b, Int.zero)) pre.
    hoare name lift (GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (ct_b, Int.zero)) pre.
    hoare name lift A_dom_lenv pre.
    hoare name lift Aop pre.
    remember ((next_tcb :: tail1 :: x1  :: (Vptr OS_PARTITION_MESSAGE_COME_ptr)  :: x3  :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil) ) as tcbcur.
    eapply seq_rule.
    { eapply assign_rule_struct_g_aop_typeneq with (tp1 :=  OS_TCB_flag)  (vl:= tcbcur);
      [  intro s; split;intros Hs;exact Hs
      | simpl; auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | simpl;auto
      | simpl; auto
      | unfold id_nth; simpl; auto
      | simpl; auto
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | symbolic_execution
      | apply assign_type_match_true; simpl; auto
      | simpl; try lia
      | simpl; auto
      | li_sepauto li ] .
      { subst. cbn. lia. } }
    (* OSTCBCur ′ → OSTCBStat =ₑ ′ OS_STAT_RDY;ₛ *)
    eapply seq_rule.
    { eapply assign_rule_struct_g_aop_typeneq with (tp1 :=  OS_TCB_flag)  (vl:= (update_nth_val 3 tcbcur Vnull));
      [  intro s; split;intros Hs;exact Hs
      | simpl; auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | simpl;auto
      | simpl; auto
      | unfold id_nth; simpl; auto
      | simpl; auto
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | symbolic_execution
      | apply assign_type_match_true; simpl; auto
      | simpl; try lia
      | simpl; auto
      | li_sepauto li ] .
      { subst. cbn. lia. } }
    (* OSTCBCur ′ → OSTCBEventPtr =ₑ 〈 OS_EVENT ∗ 〉 NULL;ₛ *)
    eapply seq_rule.
    { eapply assign_rule_struct_g_aop_typeneq with (tp1 :=  OS_TCB_flag)  (vl:= (update_nth_val 5 (update_nth_val 3 tcbcur Vnull)
    (V$ OS_STAT_RDY)));
      [  intro s; split;intros Hs;exact Hs
      | simpl; auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
      | simpl;auto
      | simpl; auto
      | unfold id_nth; simpl; auto
      | simpl; auto
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | symbolic_execution
      | apply assign_type_match_true; simpl; auto
      | simpl; try lia
      | simpl; auto
      | li_sepauto li ] .
      { subst. cbn. lia. } }
    subst. cbn [update_nth_val].
    (* qportpend_block_get (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) *)
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | | ].
    eapply qportpend_block_get_cont;eauto. go.
    (* EXIT_CRITICAL;ₛ *)
    hoare name lift Aier pre.  hoare name lift Ais pre. hoare name lift Aisr pre.
    eapply backward_rule1. eapply add_aemp_isr_is_prop;eauto.
    hoare forward prim.
    sep autocancel.
    { (* s |= ... *)
      unfold TmrInv. sep cancel HeapInv'. sep cancel TmrInv'.
      (* cancel AOSTCBPrioTbl *)
      unfold AOSTCBPrioTbl in *. 
      sep normal in H11. sep destruct H11.
      sep normal. sep eexists.
      sep cancel Aptrmapsto. sep cancel GAarray.
      sep cancel Agvarenv'. sep cancel (Aabsdata absptlsid).
      sep split;eauto.
      2,3,4,5 : sep split in H11;try auto.
      2: { clear s H17 H11.
           eapply OSQPostPure.r_priotbl_p_set_hold;eauto. }
      (* cancel  AOSTCBList *)
      instantiate (2:= tcbl2).
      instantiate (2:= (next_tcb :: tail1 :: Vnull  :: Vnull :: x3
                  :: V$ OS_STAT_RDY :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)).
      instantiate (2:= tcbl1).
      instantiate (2:= p1).
      instantiate (3:= ecbls).
      unfold AOSTCBList. sep normal. sep eexists.
      sep autocancel.
      unfold tcbdllseg. cbn [dllseg]. unfold node.
      sep normal. sep eexists. sep cancel dllseg. sep cancel Astruct.
      instantiate (5:= (set tcbls2 (ct_b, Int.zero) (curpri, rdy, Vnull, false))).
      sep split;try eauto.
      2: { (* TCBList_P *)
           eapply TCBList_P_tcb_msg2vnull_hold;eauto.
           2: eapply join_sig_get in Htcbsig;eauto.
           cbn.
           do 4 eexists.
           splits;eauto.  }
      2: { eapply join_set_r;eauto. unfold indom. eexists. eapply join_sig_get;eauto.  }
      2: { split;auto. 
           clear - Htype.
           do 11 (destruct Htype as [? Htype]).
           cbn in *. pauto. }
      (* tcbdllflag *)
      sep name lift tcbdllflag.
      sep name lift tcbdllflag in H11.
      eapply tcbdllflag_hold with (l1:= (tcbl1 ++
      (next_tcb :: tail1 :: x1  :: (Vptr OS_PARTITION_MESSAGE_COME_ptr) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil)
      :: tcbl2));eauto.
      { eapply tcbdllflag_hold_middle. cbn [eq_dllflag].
        cbn. auto. }
      sep cancel tcbdllflag.
      (*  PartitionInv *)
      sep name lift PartitionInv. 
      apply fold_PartitionInv_frm. 
      sep cancel PartitionInv_part2.
      unfold PartitionInv_part1.
      sep normal. sep eexists. 
      sep split;eauto.
      2:{ unfold RLH_PortPtrINecb. split;auto. }
      sep autocancel.
      (* EvtInv *)
      instantiate (1:= LV err @ char_t |-> errv **
      LV timeout @ Int16u |-> Vint32 tm_v **
      LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
      LV resource_get_res @ char_t |-> (V$ resn) **
      LV semaphore @ char_t |-> (V$ Z.of_nat csem) **
      LV channel @ OS_Channel ∗ |-> Vptr (cha_b, Int.zero) **
      LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
      LV dstKPort @ OS_K_Port ∗ |-> dkp_v ** LV msg_ptr @ OSMsg_t ∗ |-> Vptr msg_p ** A_dom_lenv
      ((msg_ptr, OSMsg_t ∗)
       :: (timeout, Int16u)
          :: (port_ptr, OS_Port ∗)
             :: (kport, OS_K_Port ∗)
                :: (dstKPort, OS_K_Port ∗)
                   :: (channel, OS_Channel ∗)
                      :: (semaphore, char_t)
                         :: (resource_get_res, char_t) :: (err, char_t) :: nil) ).
      sep autocancel.
      sep split in H11. 
      unfold EvtInv in *.
      sep destruct H11.
      sep normal. sep eexists. sep autocancel.
      instantiate (1:= x13). instantiate (1:= x10).
      sep name lift tcbllsegevaux.
      eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve.
      sep cancel tcbllsegevaux.
      2: { eapply tcb_linked_list_same_next_split.
      eapply tcb_linked_list_same_next_self;eauto.
      cbn. split;auto. eapply tcb_linked_list_same_next_self;eauto. }
      unfold AECBList in *.
      sep destruct H11.
      sep normal in H11.
      sep normal. sep eexists. 
      sep pauto.
      clear s H11.
      eapply ECBList_P_high_tcb_get_msg_hold;eauto. }
    { (* RH_CurTCB *)
      clear H11. unfold RH_CurTCB. do 4 eexists. erewrite get_set_eq;eauto. }
    { (* RH_TCBList_ECBList_P *)
      eapply RH_TCBList_ECBList_P_high_changem_hold;eauto.
    }
    go.
    hoare forward.
    destruct H13 as [? | [? | [? _]]];subst;clear;pauto.
  - (* branch : pend err *)
    clear H0.
    hoare forward.
    naive pure intro.
    assert (x2 <> (Vptr OS_PARTITION_MESSAGE_COME_ptr)) as Htcbmsg.
    { simpljoin1. do 4 destruct Htype as [? Htype]. clear - H4 H0.
      unfold not. intros. subst x2.
      destruct OS_PARTITION_MESSAGE_COME_ptr. 
      cbn in *. rewrite peq_true in H0. rewrite Int.eq_true in H0.  
      destruct H0;tryfalse.  }
    clear H0. 
    (* abs step *)
    destruct (get dportls p_v) as [port | ] eqn: Hdp.
    2: { partition_absrulestac port_indomainport_none_abt;apply absabort_rule. }
    destruct port as [[[[[[[pcn  pd]  pid]  pdir]  pst ] pintick ] poutick ] pt].
    assert ((pcn = Z.to_nat DNUM) \/ (pcn <> Z.to_nat DNUM)) as [ | ] by tauto.
    2: { partition_absrulestac port_indomainport_none_abt';apply absabort_rule. }
    subst pcn.
    hoare name lift AOSDomainPortPtrList pre.
    destruct Hinecb as [Hptrl Hinecb].
    eapply pptr_in_dportls1 in Hjoindp as ?;eauto.
    split_portlist. 
    rename H4 into Hdpnode. rename H5 into Hlendpl1. rename H6 into Hlendmsgl1. rename H3 into Hnprtl.
    destruct pdir.
    { exfalso. 
      eapply RL_PortAttr_dir_SOURCE in Hdpnode;eauto.
      rewrite Hdpnode in Hdir. clear - Hdir. mauto.
      rewrite nth_error_app2 by lia.
      rewrite Hlendpl1.
      rewrite Nat.sub_diag. simpl. auto. }
    destruct pt as [ ? | sz pq].
    { exfalso. 
      eapply RL_PortAttr_mode_SAMPLE in Hdpnode;eauto.
      rewrite Hdpnode in Hmode. clear - Hmode. mauto.
      rewrite nth_error_app2 by lia.
      rewrite Hlendpl1.
      rewrite Nat.sub_diag. simpl. auto. }
    partition_absrulestac port_indomainport_cont.
    unfold RH_CurTCB in Hcurtcb. destruct Hcurtcb as [curpri [st [m [sus Hcurtcb]]]].
    assert (exists wt, get ecbls p_v = Some (absport, wt)) as [wt Hportwt].
    { apply nth_error_split in Hnprtl as [? [? [? ?]]]. subst dpptrl.
      apply Forall_app in Hinecb as [? ?].
      inversion H3. auto. } 
    destruct Htcblp2 as [x [v' [tcbls2' [abstcb [? [? [Htcbsig [Htcbnode Htcblp2]]]]]]]].
    inverts H1. inverts H2. rename v' into next_tcb. 
    assert (abstcb = (curpri, st, m, sus)).
    { eapply join_sig_get in Htcbsig;eauto.
      eapply join_get_r in Htcbjoin;eauto. rewrite Htcbjoin in Hcurtcb. inverts Hcurtcb. auto. }
    subst abstcb.
    assert (m = x2).
    { unfold TCBNode_P in Htcbnode.
      simpljoin1.  clear - H1. unfold V_OSTCBMsg in H1. cbn in H1. inverts H1. auto. }
    subst x2.
    (* qportpend_after_sched (|Vptr p_v :: nil|);; *)
    assert ( (st = rdy /\ m = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port p_v) (Some Int.zero) /\ m = Vnull /\ sus = false)\/ 
      (~ ((st = rdy /\ m = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port p_v) (Some Int.zero) /\ m = Vnull /\ sus = false))))  as [ Hst | Hst ] by tauto.
    2:{ hoare name lift curtid pre.
        hoare name lift abstcblsid pre.
        hoare name lift Aop pre.
        eapply abscsq_rule';[apply noabs_oslinv | | ].
        eapply qportpend_aftersch_abt;eauto.  
        can_change_aop_solver.
        apply absabort_rule. }
    hoare name lift curtid pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | | ].
    eapply qportpend_aftersch_cont;eauto.  
    can_change_aop_solver.
    destruct Hst as [ [? [? ?]] | [? [? ?]]];[contradiction | subst ].
    assert (V_OSTCBEventPtr (next_tcb :: tail1 :: x1 :: Vnull :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil) = Some (Vptr p_v) /\ 
      V_OSTCBDly (next_tcb :: tail1 :: x1 :: Vnull :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil) =  Some (Vint32 Int.zero) 
      /\ 0 <= Int.unsigned curpri < 64 /\  
      prio_in_tbl curpri rtbl) as [Hevetptr [Htdly [Hcrpri Hpriointbl]]].
    { unfold TCBNode_P in Htcbnode.  
      clear - Htcbnode. simpljoin1. funfold H2.
      funfold H7. funfold H16.
      specialize (H16 _ _ _ _ (eq_refl _)).
      simpljoin.
      unfold RdyTCBblk in *.
      destruct H16 as [ (t & Heq & Hcase) | (Hf & Hwait)]; tryfalse.
      inverts Heq.
      destruct Hcase as [(Hnz & _) | (_ & Hz)]; tryfalse.
      simpljoin.
      splits; auto. unfold RL_TCBblk_P in *. simpljoin1. cbn in *. inverts H1. auto. }
    assert (In (ct_b, Int.zero) wt) as Hinwt.
    { clear - Htcbecb Hcurtcb Hportwt. 
      unfolds RH_TCBList_ECBList_P. destruct Htcbecb as (_ & _ & _ & _ & ?).
      unfolds RH_TCBList_ECBList_PORT_P.
      destruct H as [_ ?].
      specialize (H _ _ _ _ _ _ Hcurtcb) as [? [? ?]].
      unfold waitset, ecbid in *. 
      rewrite H in Hportwt. inverts Hportwt. auto. }
    unfold EvtInv.
    naive pure intro.
    hoare name lift osdomainportid pre.
    hoare name lift curtid pre.
    hoare name lift absecblist pre.
    hoare name lift abstcblsid pre.
    hoare name lift Aop pre.
    eapply abscsq_rule';[apply noabs_oslinv | | ].
    eapply qportpend_block_timeout_end;eauto.  
    can_change_aop_solver.
    (* OS_EventTO (­ 〈 OS_EVENT ∗ 〉 port_ptr ′­);ₛ *)
    hoare name lift AECBList pre.
    rename v'1 into ectrl. rename v'4 into msgql.
    unfold AECBList.
    naive pure intro.
    rename v'1 into headptr. rename H9 into Hecbl.
    assert (x1 = Vptr p_v). {  cbn in Hevetptr. inverts Hevetptr. auto. }
    subst x1.
    destruct p_v as [p_b p_off].
    hoare_assert_pure (isptr p1).
    { sep name lift (tcbdllseg p1) in H9.
      unfold tcbdllseg in H9. 
      eapply oscore_common.dllseg_head_isptr' in H9.
      auto. } 
    naive pure intro.
    destruct H9 as [ | (p1_v & Hptr)];[subst;tryfalse | subst ].
    hoare name lift AOSRdyTblGrp pre.
    hoare_assert_pure (RL_Tbl_Grp_P rtbl rgrp /\ prio_in_tbl (Int.repr OS_IDLE_PRIO) rtbl /\ array_type_vallist_match Tint8 rtbl /\ length rtbl = (nat_of_Z OS_RDY_TBL_SIZE)).
    { unfold AOSRdyTblGrp, AOSRdyTbl in H2.
      sep normal in H2. sep split in H2. tauto. }
    naive pure intro.
    destruct H2 as [Hlgrp [Hidelpri [Htyperltbl Hlenrtbl]]].
    assert (exists i i0 i1 i2 i3 i4,  
    (next_tcb :: tail1 :: Vptr (p_b, p_off) :: Vnull :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: nil) = 
    (next_tcb :: tail1 :: Vptr (p_b, p_off) :: Vnull :: Vint32 i :: Vint32 i0 :: Vint32 curpri ::  Vint32 i1 :: Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil)) as (i & i0 & i1 & i2 & i3 & i4 & Hcurtcbeq).
    { clear - Htype Htcbnode.
      cbn in Htcbnode. simpljoin1. inverts H0. 
      do 11 destruct Htype as [? Htype].
      cbn in *.
      destruct x3;tryfalse. destruct x4;tryfalse. destruct x6;tryfalse. destruct x7;tryfalse. destruct x8;tryfalse. destruct x9;tryfalse. 
      do 6 eexists. eauto. } 
    rewrite Hcurtcbeq in *. clear Hcurtcbeq.
    assert (exists et etbl petbl, get_ectr (Vptr (p_b, p_off)) headptr ectrl = Some (et,etbl, petbl)) as (et & etbl & petbl & Fget_ectr).
    { eapply tcb_eptr_get_ectr'; try eauto.
      cbn. do 4 eexists. splits. 3: exact Htcbsig. 3: exact Htcbnode. 1,2,3:eauto. }
    hoare name lift evsllseg pre.
    eapply backward_rule1.
    { intros s Hs. eapply get_ectr_decompose in Hs;eauto. }
    naive pure intro.
    rename v'1 into et_next. rename v'4 into ectrl1. rename v'18 into ectrl2.
    rename v'19 into msgql1. rename v'20 into msgql2. rename v'21 into portmsgq.
    destruct H2 as (Hetnext & ? &  ? & Hgetectr1 & Hgetectr2 & Hheadptr & Hnexptr ). subst.
    hoare_assert_pure (length ectrl1 = length msgql1).
    { sep name lift evsllseg in H2.
      eapply evsllseg_list_len_eq;eauto. }
    naive pure intro. rename H2 into Hleneq.
    hoare_assert_pure (V_OSEventType et = Some (V$ OS_EVENT_TYPE_PORT)).
    { sep name lift AEventNode in H2.
      eapply ecblist_p_decompose_new in Hecbl;eauto.
      destruct Hecbl as [ecbls1 [ecbls2 [Hecbl1 [Hecbl2  [Hjoinecb Hgetlast]]]]].
      cbn in Hecbl2. destruct Hecbl2 as (? & ? & ? & ? & (? & ? & ? & ? & (? & ? & ? ))).
      inverts H9.
      assert (x0 = (absport, wt)).
      { eapply join_sig_get in H13;eauto.
        eapply EcbMod.join_get_get_r in Hjoinecb;eauto.
        unfold get, EcbMap in Hportwt.
        rewrite Hportwt in Hjoinecb. inverts Hjoinecb. auto. }
      subst.  
      unfold RLH_ECBData_P in H14. destruct portmsgq;tryfalse.
      unfold AEventNode, AEventData in H2.
      sep split in H2. auto. }
    naive pure intro. rename H2 into Heventtype.
    eapply seq_rule.
    eapply call_rule';[
      cbn;unfold OS_EventTO_spec;eauto | idtac .. ].
    { unfold AEventNode, AOSEvent, node.  intros s Hs. sep normal in Hs. sep destruct Hs.
      eapply rvl_elim;[ | eapply rvl_nil]. 
      sep_get_rv.  }
    { (* ==> pre*)
      intros s Hs;unfold_spec.  unfold node.
      sep name lift aemp_isr_is in Hs. sep name lift Ais in Hs.  
      sep name lift Aisr in Hs. 
      eapply elim_aemp_isr_is_prop in Hs.
      sep normal. sep eexists. sep autocancel.
      sep pauto.
      (* RL_TCBblk_P *)
      cbn in  Htcbnode. tauto. }
    { good_frm_sovler. }
    { sep_unfold_funpost. intros s Hs. sep destruct Hs. sep auto. }
    { sep_unfold_funpre. intros s Hs. sep destruct Hs. sep auto. }
    { simpl;eauto. }
    unfold getasrt; unfold OS_EventTOPost, OS_EventTOPost'.
    naive pure intro. simpljoin1.
    inversion H2. subst v'4 v'19 v'20 v'31 v'21 v'22 v'34. clear H2.
    cbn in H9. inversion H9;subst v'18. clear H9.
    cbn in H11, H10, H12. inverts H11. inverts H10. inverts H12. 
    clear ier. 
    rename v'35 into ier. rename v'26 into ey. rename v'25 into bity. rename v'24 into bitx. rename v'23 into y.
    assert (y = curpri >>ᵢ $ 3 /\ bitx = $ 1<<ᵢ (curpri&ᵢ$ 7)).
    { clear - Htcbnode.
      cbn in *. simpljoin1. unfold RL_TCBblk_P in H1. simpljoin1.
      cbn in *.  inverts H0. inverts H3. inverts H4. auto. }
    destruct H2;subst. 
    (* EXIT_CRITICAL;ₛ *)
    hoare name lift Aier pre.  hoare name lift Ais pre. hoare name lift Aisr pre.
    eapply backward_rule1. eapply add_aemp_isr_is_prop;eauto.
    unfold AOSTCBPrioTbl. naive pure intro. rename v'4 into vhold_v.
    simpljoin1.
    hoare forward prim.
    rename H14 into Hs. 
    cbn [update_nth_val] in Hs.
    unfold AOSTCBPrioTbl, AOSTCBList.
    sep normal. eexists.
    exists tail1. eexists. exists tcbls1. exists (set tcbls2 (ct_b, Int.zero) (curpri, rdy, Vnull, false)).
    unfold tcbdllseg at 2. cbn [dllseg].
    sep normal. exists next_tcb. sep cancel node. 
    instantiate (8:= (set ecbls (p_b, p_off) (absport, remove_tid (ct_b, Int.zero) wt))).
    sep autocancel.
    sep split;try solve [cbn;auto].
    sep cancel dllseg.
    sep name lift tcbdllflag in Hs.
    sep name lift tcbdllflag.
    eapply tcbdllflag_hold with (l1:= (tcbl1 ++
    (next_tcb :: tail1 :: Vptr (p_b, p_off) :: Vnull :: Vint32 i :: Vint32 i0 :: Vint32 curpri :: Vint32 i1 :: Vint32 (curpri >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(curpri&ᵢ$ 7)) :: Vint32 bity :: nil)
    :: tcbl2));eauto.
    { eapply tcbdllflag_hold_middle. cbn [eq_dllflag].
      cbn. auto. }
    sep autocancel.
    sep name lift PartitionInv; apply fold_PartitionInv_frm.
    sep cancel PartitionInv_part2.
    unfold PartitionInv_part1. sep normal. sep eexists.
    sep autocancel.
    sep split;eauto.
    sep name lift CoreCommuInv in Hs.
    sep name lift CoreCommuInv.
    eapply CoreCommuInv_set_notsemq_frm.
    { unfold is_sem, not. intros [? [? ?]].
      clear - H14 Hportwt.
      unfold tid in *.
      rewrite H14 in Hportwt. tryfalse. }
    { unfold is_que, not. intros [? [? [? [? ?]]]].
      clear - H14 Hportwt.
      unfold tid in *.
      rewrite H14 in Hportwt. tryfalse. }
    sep cancel CoreCommuInv.
    { (* EvtInv *)
      unfold EvtInv, AECBList. sep normal. sep eexists. sep autocancel.
      sep name lift (evsllseg et_next) in Hs. sep name lift AEventNode in Hs.
      eapply evsllseg_add_head in Hs;eauto.
      sep name lift (evsllseg headptr) in Hs.
      eapply ucos_common.evsllseg_app in Hs;eauto.
      sep autocancel.
      2: { unfold V_OSEventListPtr in *. erewrite nth_upd_neqrev;eauto. }
      instantiate (3:= v'10). instantiate (4:= v'9). instantiate (5:= v'8).
      sep split;auto.
      eapply ASemEIBs_port_set_ecbls_preserve;eauto.
      sep cancel ASemEIBs.
      eapply AMuxEIBs_port_set_ecbls_preserve with (capl := mcapl);eauto.
      sep cancel AMuxEIBs.
      eapply AMqEIBs_port_set_ecbls_preserve;eauto.
      sep cancel AMqEIBs.
      eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve;eauto.
      eapply tcb_linked_list_same_next_split.
      eapply tcb_linked_list_same_next_self;eauto.
      cbn. split;auto. eapply tcb_linked_list_same_next_self;eauto.
      { (* Q_ECB_P *)
        eapply mq_ecb_p_sem_set_ecbls_port_preserve;eauto. }
      { (* MUX_ECB_P *)
        eapply mux_ecb_p_port_set_preserve;eauto. }
      { (* SEM_ECB_P *)
        eapply sem_ecb_p_mutex_set_preserve;eauto. }
      clear s Hs.
      eapply ECBList_P_hold_for_update_port_to_rdy;eauto. }
    { (*RLH_PortPtrINecb *)
      split;auto.
      clear -Hinecb.
      eapply Forall_forall.
      intros.
      eapply Forall_forall in Hinecb;eauto.
      assert (x = (p_b, p_off) \/ x <> (p_b, p_off)) as [ | ] by tauto.
      subst. eexists. erewrite get_set_eq. eauto.
      destruct Hinecb. erewrite get_set_neq; eauto. }
    { (* R_PrioTbl_P *)
      eapply R_PrioTbl_P_hold1;eauto. }
    { (* TCBList_P *)
      cbn. clear Hs. 
      simpljoin1.
      do 3 eexists. exists (curpri, rdy, Vnull, false).
      splits;eauto.
      - eapply join_sig_set;eauto.
      - change (next_tcb :: tail1 :: Vnull :: Vnull :: Vint32 i ::  V$ OS_STAT_RDY :: Vint32 curpri :: Vint32 i1 :: Vint32 (curpri >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(curpri&ᵢ$ 7)) :: Vint32 bity :: nil) with 
      (update_nth_val 5 (update_nth_val 2 (next_tcb :: tail1 :: Vptr (p_b, p_off) :: Vnull :: Vint32 i :: Vint32 i0 :: Vint32 curpri :: Vint32 i1 :: Vint32 (curpri >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(curpri&ᵢ$ 7)) :: Vint32 bity :: nil) Vnull) (V$ OS_STAT_RDY)).
      assert (He1': 0 <= Int.unsigned (curpri >>ᵢ $ 3) <= 7). { 
        clear - H18 H17. mauto. }
      lets Hgrp: array_type_match_get_value He1' Htyperltbl Hlenrtbl.
      destruct Hgrp as [z Hgrp].
      eapply TCBNode_P_hold_update_2rdy with (tcbls := tcbls2);eauto.
      cbn;auto. 
      instantiate (1:= (ct_b, Int.zero)). clear - Htcbsig.  eapply TcbMod.join_sig_get;eauto. unfold TcbJoin in Htcbsig. eauto. }
  { eapply join_set_r;eauto.
    unfold indom. eexists. eapply join_sig_get;eauto. }
  { (* RH_CurTCB *)
    unfold RH_CurTCB.
    do 4 eexists. eapply get_set_eq;eauto. }
  { (* RH_TCBList_ECBList_P *)
    eapply RH_TCBList_ECBList_P_hold_for_port_to_rdy;eauto. }
  go.
  (* RETURN 〈 char_t 〉 ′ OS_TIMEOUT  *)
  hoare forward.
Qed.
  