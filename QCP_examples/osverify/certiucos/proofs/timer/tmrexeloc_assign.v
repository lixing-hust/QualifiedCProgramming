Require Import ucos_include.
Require Import Lia.

Require Import sep_combine_lemmas_added.
Require Import tmr_aux.
Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.

Open Scope code_scope.

Open Scope int_scope.

Lemma OStimer_exeloc_assign_locz : forall 
r ri aop ls __locz locv'
(p':asrt )
(tid: tid)
(i: int32)
(p1  p2: val)
(tcbl1: list vallist)
(curtcb: vallist)
(tcbl2: list vallist)
(rtbl: vallist)
(tcbls: TcbMod.map)
(locl1: list val)
(locv: val)
(locl2: list val) 
(pnext: val),
symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
length locl1 = length tcbl1 ->
length locl2 = length tcbl2 ->
V_OSTCBNext curtcb = Some pnext ->
array_type_vallist_match Int32u (locl1 ++ locv :: locl2) ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{dllsegloc p1 (Vptr tid) tcbl1 locl1 V_OSTCBNext **
  PV get_off_addr tid loc_off @ Int32u |-r-> locv **
  dllsegloc pnext Vnull tcbl2 locl2 V_OSTCBNext **
  AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl tid tcbls **
   <|| aop ||>  **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid (init_lg' locv') **
  A_dom_lenv ls **
  p'}} 
  OSTCBCur′→OSTCBLoc =ₑ (′__locz ≪ ′4) +ₑ os_code_defs.timerid′
{{ AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) (locl1 ++ (Vint32 (($ __locz) <<ᵢ ($ 4) +ᵢ i)) :: locl2) **
  AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl tid tcbls **
  <|| aop ||>  **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid (init_lg' (($ __locz<<ᵢ$ 4) +ᵢ  i))**
  A_dom_lenv ls **
  p' }}.
Proof.
  intros.
  unfold AOSTCBList.
  unfold p_local at 1, LINV, OSLInv at 2, init_lg' at 1.
  hoare normal pre.
  pure_intro.
  inverts H4.
  apply array_type_vallist_match_app in H3 as [H3_ [H3_0 H3]].
  simpl in H3_0. destruct locv;tryfalse. clear H3_0.
  hoare lifts (2::8::nil)%nat pre. 
  eapply backward_rule1.
  { intros.
    sep remember (1::2::nil)%nat in H4.
    sep remember (3::nil)%nat in H4.
    subst H10 H12.
    eapply astar_mono in H4.
    2: {intros ? Hs; exact Hs. }
    2: { apply sep_combine_lemmas.PV_combine_ro. }
    exact H4. }
  pure intro.
  hoare remember (8::13::nil)%nat pre.
  hoare lifts (1::3::nil)%nat pre.
  eapply forward_rule2.
  eapply assign_rule.
  { instantiate (1:= Int32u). 
    eapply eq_int. tauto. }
  { subst H10;split.
   apply addrof_rv_to_lv. 
   destruct tid. unfold get_off_addr.
   eapply symbolic_lemmas.struct_offset_rv;[ |
   reflexivity| | ].
   { eapply symbolic_lemmas.addrof_deref_rv.
   sep lifts (10::4::nil)%nat in H10.
   eapply symbolic_lemmas.gvar_rv;eauto. }
   { unfold loc_off, field_offset. simpl. 
   clear. pauto. }
   { cbn;auto. }
   symbolic_execution. }
  { subst H10. intros.
    sep lift 12%nat in H10.
    apply sep_combine_lemmas.PV_separate_rw_frm in H10.
    unfold CurLINV,LINV, OSLInv.
    sep auto. }

  subst H10.
  assert (Int.ltu ($ 4) Int.iwordsize = true) by pauto.
  rewrite H10.
  cbn [val_inj add val_inj].
  intros.
  sep normal in H12.
  sep lift 13%nat in H12.
  apply sep_combine_lemmas.PV_separate_rw_frm in H12.
  sep lifts (6::8::9::1::10::nil)%nat in H12.
  apply dllsegloc_merge_locvl_frm in H12;auto.
  unfold AOSTCBLoc, p_local, LINV, OSLInv.
  sep auto;eauto.
  apply array_type_vallist_match_app. split;cbn;eauto.
Qed.

Lemma OStimer_exeloc_assign_zero : forall 
r ri aop ls  locv'
(p':asrt )
(tid: tid)
(p1  p2: val)
(tcbl1: list vallist)
(curtcb: vallist)
(tcbl2: list vallist)
(rtbl: vallist)
(tcbls: TcbMod.map)
(locl1: list val)
(locv: val)
(locl2: list val) 
(pnext: val),
symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
length locl1 = length tcbl1 ->
length locl2 = length tcbl2 ->
V_OSTCBNext curtcb = Some pnext ->
array_type_vallist_match Int32u (locl1 ++ locv :: locl2) ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{dllsegloc p1 (Vptr tid) tcbl1 locl1 V_OSTCBNext **
  PV get_off_addr tid loc_off @ Int32u |-r-> locv **
  dllsegloc pnext Vnull tcbl2 locl2 V_OSTCBNext **
  AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl tid tcbls **
   <|| aop ||>  **
  p_local OSLInv tid (init_lg' locv') **
  A_dom_lenv ls **
  p'}} 
  OSTCBCur′→OSTCBLoc =ₑ ′0
{{ AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) (locl1 ++ (Vint32 Int.zero) :: locl2) **
  AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl tid tcbls **
  <|| aop ||>  **
  p_local OSLInv tid init_lg**
  A_dom_lenv ls **
  p' }}.
Proof.
  intros.
  unfold AOSTCBList.
  unfold p_local at 1, LINV, OSLInv at 2, init_lg' at 1.
  hoare normal pre.
  pure_intro.
  inverts H4.
  apply array_type_vallist_match_app in H3 as [H3_ [H3_0 H3]].
  simpl in H3_0. destruct locv;tryfalse. clear H3_0.
  hoare lifts (2::8::nil)%nat pre. 
  eapply backward_rule1.
  { intros.
    sep remember (1::2::nil)%nat in H4.
    sep remember (3::nil)%nat in H4.
    subst H10 H12.
    eapply astar_mono in H4.
    2: {intros ? Hs; exact Hs. }
    2: { apply sep_combine_lemmas.PV_combine_ro. }
    exact H4. }
  pure intro.
  hoare remember (8::12::nil)%nat pre.
  hoare lifts (1::3::nil)%nat pre.
  eapply forward_rule2.
  eapply assign_rule.
  { instantiate (1:= Int32u). 
    eapply eq_int. tauto. }
  { subst H10;split.
   apply addrof_rv_to_lv. 
   destruct tid. unfold get_off_addr.
   eapply symbolic_lemmas.struct_offset_rv;[ |
   reflexivity| | ].
   { eapply symbolic_lemmas.addrof_deref_rv.
   sep lifts (9::4::nil)%nat in H10.
   eapply symbolic_lemmas.gvar_rv;eauto. }
   { unfold loc_off, field_offset. simpl. 
   clear. pauto. }
   { cbn;auto. }
   symbolic_execution. }
  { subst H10. intros.
    sep lift 11%nat in H10.
    apply sep_combine_lemmas.PV_separate_rw_frm in H10.
    unfold CurLINV,LINV, OSLInv.
    sep auto. }

  subst H10.
  cbn [val_inj add val_inj].
  intros.
  sep normal in H10.
  sep lift 12%nat in H10.
  apply sep_combine_lemmas.PV_separate_rw_frm in H10.
  sep lifts (6::8::9::1::10::nil)%nat in H10.
  apply dllsegloc_merge_locvl_frm in H10;auto.
  unfold AOSTCBLoc, p_local, LINV, OSLInv.
  sep auto;eauto.
  apply array_type_vallist_match_app. split;cbn;eauto.
Qed.


Lemma PV_p_local_locv_eq : forall tid locv locv',
  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv' **
  p_local OSLInv tid init_lg  ==> 
  [| locv' =  locv |] **  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv' **
  p_local OSLInv tid init_lg.
Proof.
  intros.
  sep split.
  sep auto.
  unfold p_local ,LINV, OSLInv, init_lg' in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H0.
  inversion H0.
  simpljoin1.
  sep lifts (3::2::nil)%nat in H.
  apply sep_combine_lemmas.PV_combine_ro_frm in H.
  sep split in H.
  apply rule_type_val_match_encode_val_eq in H0.
  2,3 : pauto.
  inversion H0.
  auto.
Qed.

Lemma PV_p_local_locv_eq_frm : forall tid locv locv' p,
  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv' **
  p_local OSLInv tid init_lg ** p ==> 
  [| locv' =  locv |] **  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv' **
  p_local OSLInv tid init_lg ** p.
Proof.
  intros.
  sep cancel p. 
  apply PV_p_local_locv_eq;auto.
Qed.