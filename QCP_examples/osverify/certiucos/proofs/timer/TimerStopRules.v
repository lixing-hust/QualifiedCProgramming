Require Import ucos_include.
Require Import Lia.



(*
Lemma TMRcntList_stop_preserve:
  forall tmrl lowl highl n tmrn tmr,
    TMRNode_P tmrn tmr ->
    nth_error tmrl n = Some tmrn ->
    TMRcntList_P tmrl lowl highl ->
    TMRcntList_P 
    (update_nth_vallist n tmrl (lop_stop tmrn)) lowl highl.
Proof. 
  induction tmrl;intros.
  - destruct n;tryfalse.
  - destruct n. 
    + cbn [nth_error update_nth_vallist] in *.
      inversion H0. subst a.
      unfold TMRcntList_P  in *.
      destruct H1.
      cbn [map] in *.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_stop binaryop_nth_val];auto.
      subst lowl highl. 
      unfold TMRNode_P in H.
      my_destruct H.
      lets Hmode : Pmode_isGPorWDtmr H.
      unfold lop_stop.
      destruct Hmode.
      * rewrite H5. auto.
      * destruct H5. rewrite H5,H6. auto.
    + cbn [update_nth_vallist ].
      unfold TMRcntList_P  in *.
      destruct H1.
      cbn [map] in *.
      subst lowl highl. 
      simpl in H0.
      pose proof IHtmrl (map V_OSCNTLO' tmrl) (map V_OSCNTHI' tmrl) _ _ _ H H0.
      specialize (H1 ltac:(split;congruence)).
      destruct H1.
      rewrite H1,H2.
      auto.
Qed.
Lemma Taskexeloc_P_get_set_stop:
  forall vl tmrls crevl crevh i prd em st tick om,
    get tmrls (Int.unsigned i) = Some (gp_t prd em, st, tick, om) ->
    Taskexeloc_P vl tmrls crevl crevh ->
    Taskexeloc_P vl (set tmrls (Int.unsigned i) (hop_stop (gp_t prd em, st, tick, om))) 
     crevl crevh.
Proof.
  induction vl;intros.
  - cbn [Taskexeloc_P]. auto.
  - cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H0.
  splits.
  2: eapply IHvl;eauto.
  cbn [hop_stop].
  assert (isgptmr (gp_t prd em, tm_idle, tick, om, hid) = true) by (cbn;auto).
  unfold Taskexeloc_Node_P in *.
  destruct (Int.eq i0 Int.zero);auto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrstart_gettgcr)).
   my_destruct H0. eapply get_get_set_andp with (b:=x);eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrstop_gettgcr)).
   my_destruct H0. eapply get_get_set_andp with (b:=x);eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_getloaddr)).
   my_destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_gethiaddr)).
   destruct H0. eapply get_get_set;eauto.

  remember (Int.unsigned (i0&ᵢ$ 15)) as atmrid.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_getlo)).
  { my_destruct H0.
   assert ((Int.unsigned i) = atmrid \/ (Int.unsigned i) <> atmrid) by lia.
   destruct H5. rewrite H5 in *.
     {  pose proof map_get_unique H H0.
       inversion H6. substs.
       do 5 eexists. split;auto.
       apply get_set_eq.
       auto. }
     { do 5 eexists.
       split. 
       erewrite map_get_set';eauto.
       auto. }
   }
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrreset_gettgcr)).
  destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrreset_gettcr)).
   destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrreset_settgcr)).
   destruct H0. eapply get_get_set;eauto.
  auto.
Qed.

Lemma Taskexeloc_P_update_midlle_preserve_stop :
forall vl1 v vl2 tmrls crevl crevh i prd em st tick om hid,
  Taskexeloc_P (vl1 ++ v :: vl2) tmrls crevl crevh ->
  get tmrls (Int.unsigned i) = Some (gp_t prd em, st, tick, om, hid) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_P (vl1 ++ (Vint32 (($ __OSLoc_tmrstop_gettgcr<<ᵢ$ 4) +ᵢ  i)) :: vl2 ) tmrls crevl crevh.
Proof.
  induction vl1;intros.
  - simpl in *. 
    destruct v;tryfalse.
    destruct H.
    split;auto.
    clear - H0 H1 H2.
    solve_ExeNodeP.
  - simpl ((_ :: _) ++ _ ) in *.
    cbn [update_nth_val Taskexeloc_P] in *.
    destruct a;tryfalse.
    destruct H.
    split;auto.
    eapply IHvl1;eauto.
Qed. *)

(* Lemma Taskexeloc_P_eq___OSLoc_tmrstop_gettgcr :
forall vl tmrls crevl crevh n i,
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_val' n vl = Vint32 (($ __OSLoc_tmrstop_gettgcr<<ᵢ$ 4) +ᵢ  i)
  -> Taskexeloc_P vl tmrls crevl crevh -> (exists tmri, get tmrls  (Int.unsigned i) = Some tmri /\ isgptmr tmri = true ).
Proof.
  induction vl;intros.
  -  destruct n;cbn [nth_val' Taskexeloc_P] in *;tryfalse. 
  -  
  assert (7 < Int.unsigned i )%Z. {
  assert (7%Z = Int.unsigned ($ 7)) by pauto.
  rewrite H3. apply Intlt_true_is_Zlt;auto. }
  assert (Int.unsigned i <16)%Z. {
  assert (16%Z = Int.unsigned ($ 16)) by pauto.
  rewrite H4. apply Intlt_true_is_Zlt;auto. }

  assert (((($ __OSLoc_tmrstop_gettgcr <<ᵢ $ 4) +ᵢ  i) >>ᵢ $ 4) = $ __OSLoc_tmrstop_gettgcr).  
  { clear - H4. unfold __OSLoc_tmrstop_gettgcr in *. mauto. }
  assert ((Int.unsigned
  ((($ __OSLoc_tmrstop_gettgcr<<ᵢ$ 4) +ᵢ  i)&ᵢ$ 15)) = Int.unsigned i).  
  { clear -H4.  unfold __OSLoc_tmrstop_gettgcr in *. mauto. }
  cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H2.
  destruct n;cbn [nth_val' ] in H1.
  + inversion H1. subst.
    unfold Taskexeloc_Node_P in H2.
    rewrite H5 in *.
    assert (Int.eq (($ __OSLoc_tmrstop_gettgcr<<ᵢ$ 4) +ᵢ  i)
    Int.zero = false). 
    {  unfold __OSLoc_tmrstop_gettgcr.
      apply int_ltu_eq_false.
      clear - H H0 H3 H4.
      mauto. }
      rewrite H8 in *; clear H8. 
    assert (Int.eq ($ __OSLoc_tmrstop_gettgcr)
    ($ __OSLoc_tmrstart_gettgcr) = false) by pauto.
    rewrite H8 in *; clear H8. 
    assert (Int.eq ($ __OSLoc_tmrstop_gettgcr)
    ($ __OSLoc_tmrstop_gettgcr) = true) by pauto.
    rewrite H8 in *; clear H8. 
    rewrite H6 in *.
    apply H2. 
  + eapply IHvl;eauto.
Qed. *)

(* Lemma AOSTMRList_update_stop : 
  forall (tmrl : list vallist) (tmrls: TmrMod.map) tmri i tmr,
  length tmrl = 16%nat ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_error tmrl (Z.to_nat (Int.unsigned i)) = Some tmri ->
  get tmrls (Int.unsigned i) = Some tmr ->
  RLH_TMRList_P tmrl tmrls ->
  RLH_TMRList_P (update_nth_vallist (Z.to_nat (Int.unsigned i)) tmrl 
  (lop_stop tmri)) (set tmrls (Int.unsigned i) (hop_stop tmr)).
Proof.
  intros.
  unfold RLH_TMRList_P in *. 
  pose proof TMRList_P'_update_tmr tmrl tmrls tmri 0%nat (Z.to_nat (Int.unsigned i)) tmr stop_tmrop H2.
  simpl in H5.
  erewrite Z2Nat.id in *.
  apply H5;eauto. 
  assert (Int.unsigned i < 16)%Z. 
  { assert (Int.unsigned ($ 16) = 16)%Z by pauto.
    rewrite <- H6.
    apply Intlt_true_is_Zlt;auto. }
  rewrite H. lia.
  assert (7 < Int.unsigned i)%Z. 
  { assert (Int.unsigned ($ 7) = 7)%Z by pauto.
    rewrite <- H6.
    apply Intlt_true_is_Zlt;auto. }
    lia.
Qed. *)
(*
Lemma OStimer_stopProofPart0 : forall 
p' s
(tid: tid)
(i: int32)
(v'2: val)
(H: val_inj
      (bool_and
         (val_inj
            (if Int.ltu ($ 7) i then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))
         (val_inj
            (if Int.ltu i ($ 16) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))) <>
    Vint32 Int.zero)
(H0: val_inj
       (bool_and
          (val_inj
             (if Int.ltu ($ 7) i then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))
          (val_inj
             (if Int.ltu i ($ 16) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))) <>
     Vnull)
(H1: val_inj
       (bool_and
          (val_inj
             (if Int.ltu ($ 7) i then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))
          (val_inj
             (if Int.ltu i ($ 16) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))) <>
     Vundef)
,
{|OS_spec, GetHPrio, OSLInv, I,
fun x : option val =>
(( <|| END x ||>  **
  p_local OSLInv tid init_lg **
  ((EX v : val, LV os_code_defs.timerid @ Int32u |-> v) **
   (EX v : val, LV err @ Int32u |-> v) **
   (EX v : val, LV ret @ Int32u |-> v) **
   (EX v : val, LV Timer_TGCR @ (Int32u) ∗ |-> v) ** Aemp) **
  Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
 A_dom_lenv
   ((os_code_defs.timerid, Int32u)
    :: (err, Int32u)
       :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)) **
tmrcnt_pp, Afalse|}|- tid
{{ <|| s ||>  **
  timerregVar **
  LV Timer_TGCR @ (Int32u) ∗ |-> v'2 **
  A_dom_lenv
    ((os_code_defs.timerid, Int32u)
     :: (err, Int32u)
        :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil) **
  p_local OSLInv tid init_lg **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i
     ** p' }} 
Timer_TGCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 9 +ₑ (os_code_defs.timerid ′ ≪ ′ 14)) {{ 
<|| s ||>   **
  timerregVar **
  LV Timer_TGCR @ (Int32u) ∗ |-> Vptr (timer_TGCR i) **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv
    ((os_code_defs.timerid, Int32u)
     :: (err, Int32u) :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)
     ** p' }}.
Proof.
  intros.
  unfold timerregVar.
  unfold timer_TGCR.
  destruct tmrRegsAddr eqn: Htmraddr.
  eapply forward_rule2.
  { hoare_assign. }
  assert ( Int.ltu ($ 14) Int.iwordsize = true) by pauto.
  rewrite H2.
  cbn [val_inj].
  intros.
  sep cancel p_local.
  sep cancel A_dom_lenv.
  sep cancel p'.
  sep auto.
  sep lift 2%nat.
  eapply astar_mono.
  3: apply H3.
  2: sep auto.
  unfold get_off_addr.
  cbn [ fst snd].
  assert ((i0 +ᵢ  Int.mul ($ 9) ($ 4)) +ᵢ  Int.mul (i<<ᵢ$ 14) ($ 4) = (i0 +ᵢ  $ 36) +ᵢ  Int.mul i ($ 65536)).
  { eapply Timer_TGCR_off_eq;eauto. pauto. 
  }
  rewrite H4. auto.
Qed. *)

(* Lemma OStimer_stopProofPart1 : forall 
(p':asrt ) aop 
(tid: tid)
(i: int32)
(v'9  v'10: val)
(v'11: list vallist)
(v'12: vallist)
(v'13: list vallist)
(v'14: vallist)
(v'15: val)
(v'16: EcbMod.map)
(v'17: TcbMod.map)
(v'18: int32)
(v'19: addrval)
(v'20: val)
(v'21: list vallist)
(v'22: int32)
(v'23: absinthandler)
(v'24: list vallist)
(v'25: TmrMod.map)
(v'26: list (addrval * nat * list val))
(v'27: list (addrval * type * val))
(v'28: vallist)
(v'29 v'30: list val)
(prd: timerperiod)
(em: enable_mode)
(st: timerstatus)
(tick: timertick)
(om: outMode)
(hid: option handlerid)
(v'40: list val)
(v'41: val)
(v'42: list val) 
(v'43: val),
Taskexeloc_P (v'40 ++ v'41 :: v'42) v'25 v'29 v'30 -> 
get v'25 (Int.unsigned i) = Some (gp_t prd em, st, tick, om, hid) ->
Int.ltu ($ 7) i = true -> 
Int.ltu i ($ 16) = true ->
length v'40 = length v'11 ->
length v'42 = length v'13 ->
V_OSTCBNext v'12 = Some v'43 ->
array_type_vallist_match Int32u (v'40 ++ v'41 :: v'42) ->
{|OS_spec, GetHPrio, OSLInv, I,
fun x : option val =>
(( <|| END x ||>  **
  p_local OSLInv tid init_lg **
  ((EX v : val, LV os_code_defs.timerid @ Int32u |-> v) **
   (EX v : val, LV err @ Int32u |-> v) **
   (EX v : val, LV ret @ Int32u |-> v) **
   (EX v : val, LV Timer_TGCR @ (Int32u) ∗ |-> v) ** Aemp) **
  Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
 A_dom_lenv
   ((os_code_defs.timerid, Int32u)
    :: (err, Int32u)
       :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)) **
tmrcnt_pp, Afalse|}|- tid
{{dllsegloc v'9 (Vptr tid) v'11 v'40 V_OSTCBNext **
  PV get_off_addr tid loc_off @ Int32u |-r-> v'41 **
  dllsegloc v'43 Vnull v'13 v'42 V_OSTCBNext **
  AOSTCBList v'9 v'10 v'11 (v'12 :: v'13) v'14 tid v'17 **
  <|| aop ||> **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv
    ((os_code_defs.timerid, Int32u)
     :: (err, Int32u) :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)  **
  p'}} 
  OSTCBCur′→OSTCBLoc =ₑ (′__OSLoc_tmrstop_gettgcr ≪ ′4) +ₑ os_code_defs.timerid′
{{ [|Taskexeloc_P (v'40 ++ (Vint32 (($ __OSLoc_tmrstop_gettgcr) <<ᵢ ($ 4) +ᵢ i)) :: v'42) v'25 v'29 v'30 |] **
  AOSTCBLoc v'9 (v'11 ++ v'12 :: v'13) (v'40 ++ (Vint32 (($ __OSLoc_tmrstop_gettgcr) <<ᵢ ($ 4) +ᵢ i)) :: v'42) **
  AOSTCBList v'9 v'10 v'11 (v'12 :: v'13) v'14 tid v'17 **
  <|| aop ||> **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid (init_lg' (($ __OSLoc_tmrstop_gettgcr<<ᵢ$ 4) +ᵢ  i))**
  A_dom_lenv
  ((os_code_defs.timerid, Int32u)
   :: (err, Int32u) :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)  **
  p' }}.
Proof.
  intros.
  unfold AOSTCBList.
  unfold p_local at 2, LINV, OSLInv at 3, init_lg' at 2.
  hoare normal pre.
  pure intro.
  inverts H7.
  apply array_type_vallist_match_app in H6 as [H6_ [H6_0 H6]].
  simpl in H6_0. destruct v'41;tryfalse. clear H6_0.
  hoare lifts (2::8::nil)%nat pre. 
  eapply backward_rule1.
  { intros.
    sep remember (1::2::nil)%nat in H7.
    sep remember (3::nil)%nat in H7.
    subst H13 H15.
    eapply astar_mono in H7.
    2: {intros ? Hs; exact Hs. }
    2: { apply sep_combine_lemmas.PV_combine_ro. }
    exact H7. }
  pure intro.
  hoare remember (8::13::nil)%nat pre.
  hoare lifts (1::3::nil)%nat pre.
  eapply forward_rule2.
  eapply assign_rule.
  { instantiate (1:= Int32u). 
    eapply eq_int. tauto. }
  {subst H13;split.
   apply addrof_rv_to_lv. 
   destruct tid. unfold get_off_addr.
   eapply symbolic_lemmas.struct_offset_rv;[
   symbolic_execution|
   reflexivity| | simpl;auto ].
   { unfold loc_off, field_offset. simpl. 
   clear. pauto. }
   symbolic_execution. }
  { subst H13. intros.
    sep lift 12%nat in H13.
    apply sep_combine_lemmas.PV_separate_rw_frm in H13.
    unfold CurLINV,LINV, OSLInv.
    sep auto. }

  subst H13.
  assert (Int.ltu ($ 4) Int.iwordsize = true) by pauto.
  rewrite H13.
  cbn [val_inj add val_inj].
  intros.
  apply astar_l_apure_intro.
  sep normal in H15.
  sep lift 13%nat in H15.
  apply sep_combine_lemmas.PV_separate_rw_frm in H15.
  sep lifts (6::8::9::1::10::nil)%nat in H15.
  apply dllsegloc_merge_locvl_frm in H15;auto.
  unfold AOSTCBLoc, p_local, LINV, OSLInv.
  sep auto;eauto.
  apply array_type_vallist_match_app. split;cbn;eauto.

  eapply Taskexeloc_P_update_midlle_preserve_stop;eauto.
Qed. *)



  