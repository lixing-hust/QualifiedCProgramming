Require Import ucos_include.
Require Import Lia.

Require Import sep_combine_lemmas_added.
Require Import tmr_aux.
Require Import tmr_rules.
Require Import tmr_sep_rules.

Open Scope code_scope.

Open Scope int_scope.

(* Lemma TMRcntList_start_preserve:
  forall tmrl lowl highl n tmrn tmr,
    TMRNode_P tmrn tmr ->
    nth_error tmrl n = Some tmrn ->
    TMRcntList_P tmrl lowl highl ->
    TMRcntList_P 
    (update_nth_vallist n tmrl (lop_start tmrn)) lowl highl.
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
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      destruct tmrn.
        cbn [lop_start binaryop_nth_val];auto.
      subst lowl highl. 
      unfold TMRNode_P in H.
      my_destruct H.
      lets Hmode : Pmode_isGPorWDtmr H.
      unfold lop_start.
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
Qed. *)



(* Lemma Taskexeloc_Node_P_start :
forall tmrls crevl crevh i t0 t1 t o,
  get tmrls (Int.unsigned i) = Some (t0,t1,t,o) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_Node_P (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i) tmrls crevl crevh.
Proof.
  intros.
  assert (7 < Int.unsigned i )%Z. 
  { assert (7%Z = Int.unsigned ($ 7)) by pauto.
    rewrite H2. apply Intlt_true_is_Zlt;auto. }
  assert (Int.unsigned i <16)%Z. 
  { assert (16%Z = Int.unsigned ($ 16)) by pauto.
    rewrite H3. apply Intlt_true_is_Zlt;auto. }
  assert (((($ __OSLoc_tmrstart_gettgcr <<ᵢ $ 4) +ᵢ  i) >>ᵢ $ 4) = $ __OSLoc_tmrstart_gettgcr).  
  { clear - H3. unfold __OSLoc_tmrstart_gettgcr in *. mauto. }
  assert ((Int.unsigned
  ((($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)&ᵢ$ 15)) = Int.unsigned i).  
  { clear -H3.  unfold __OSLoc_tmrstart_gettgcr in *. mauto. }
  unfold Taskexeloc_Node_P.
  rewrite H4 in *.
  rewrite H5 in *.
  assert (Int.eq (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)
  Int.zero = false). 
  {  unfold __OSLoc_tmrstart_gettgcr.
    apply int_ltu_eq_false.
    clear - H1 H2 H3 H4.
    mauto. }
  rewrite H6 in *; clear H6. 
  assert (Int.eq ($ __OSLoc_tmrstart_gettgcr)
  ($ __OSLoc_tmrstart_gettgcr) = true) by pauto.
  rewrite H6 in *; clear H6.  
  exists ((t0, t1, t, o));auto.
Qed. *)

(* Lemma Taskexeloc_P_update_midlle_preserve_start :
forall vl1 v vl2 tmrls crevl crevh i t0 t1 t o,
  Taskexeloc_P (vl1 ++ v :: vl2) tmrls crevl crevh ->
  get tmrls (Int.unsigned i) = Some (t0,t1,t,o) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_P (vl1 ++ (Vint32 (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)) :: vl2 ) tmrls crevl crevh.
Proof.
  induction vl1;intros.
  - simpl in *. 
    destruct v;tryfalse.
    destruct H.
    split;auto.
    eapply Taskexeloc_Node_P_start;eauto.
  - simpl ((_ :: _) ++ _ ) in *.
    cbn [update_nth_val Taskexeloc_P] in *.
    destruct a;tryfalse.
    destruct H.
    split;auto.
    eapply IHvl1;eauto.
Qed. *)
(* 
Lemma Taskexeloc_P_get_set_start:
forall vl tmrls crevl crevh i prd em st tick om,
  get tmrls i = Some (gp_t prd em, st, tick, om) ->
  Taskexeloc_P vl tmrls crevl crevh ->
  Taskexeloc_P vl (set tmrls i (hop_start (gp_t prd em, st, tick, om))) crevl crevh.
Proof.
  induction vl;intros.
  - cbn [Taskexeloc_P]. auto.
  - cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H0.
  splits.
  2: eapply IHvl;eauto.
  unfold Taskexeloc_Node_P in *.
  destruct (Int.eq i0 Int.zero);auto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrstart_gettgcr)).
   destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrstop_gettgcr)).
   destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_getloaddr)).
   destruct H0. eapply get_get_set;eauto.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_gethiaddr)).
   destruct H0. eapply get_get_set;eauto.
   
  destruct tmri. destruct p. destruct p. cbn [hop_start].
  remember (Int.unsigned (i0&ᵢ$ 15)) as atmrid.
  destruct (Int.eq (i0 >>ᵢ $ 4) ($ __OSLoc_tmrget_getlo)).
   { do 4 destruct H0.
   destruct H0.
   assert (i = atmrid \/ i <> atmrid) by lia.
   destruct H3. subst i.
     { pose proof @map_get_unique.
       specialize (H3 _ _ _ _ _ _ _ _ H H0).
       inversion H3. subst t0 t1 t o.
       exists x tm_start x1 x2. split;auto.
       apply get_set_eq. }
     { exists x x0 x1 x2.
       erewrite map_get_set';auto. }
   }
   auto.
Qed. *)

(* Lemma Taskexeloc_P_eq___OSLoc_tmrstart_gettgcr :
forall vl tmrls crevl crevh n i,
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_val' n vl = Vint32 (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)
  -> Taskexeloc_P vl tmrls crevl crevh -> (exists tmri, get tmrls  (Int.unsigned i) = Some tmri).
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

  assert (((($ __OSLoc_tmrstart_gettgcr <<ᵢ $ 4) +ᵢ  i) >>ᵢ $ 4) = $ __OSLoc_tmrstart_gettgcr).  
  { clear - H4. unfold __OSLoc_tmrstart_gettgcr in *. mauto. }
  assert ((Int.unsigned
  ((($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)&ᵢ$ 15)) = Int.unsigned i).  
  { clear -H4.  unfold __OSLoc_tmrstart_gettgcr in *. mauto. }
  cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H2.
  destruct n;cbn [nth_val' ] in H1.
  + inversion H1. subst.
    unfold Taskexeloc_Node_P in H2.
    rewrite H5 in *.
    assert (Int.eq (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i)
    Int.zero = false). 
    {  unfold __OSLoc_tmrstart_gettgcr.
      apply int_ltu_eq_false.
      clear - H H0 H3 H4.
      mauto. }
      rewrite H8 in *; clear H8. 
    assert (Int.eq ($ __OSLoc_tmrstart_gettgcr)
    ($ __OSLoc_tmrstart_gettgcr) = true) by pauto.
    rewrite H8 in *. rewrite H6 in *.
    apply H2. 
  + eapply IHvl;eauto.
Qed. *)

(* Lemma AOSTMRList_update_start : 
  forall (tmrl : list vallist) (tmrls: TmrMod.map) tmri i tmr p,
  length tmrl = 16%nat ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_error tmrl (Z.to_nat (Int.unsigned i)) = Some tmri ->
  get tmrls (Int.unsigned i) = Some tmr ->
  AOSTMRList tmrl tmrls ** p ==>
  AOSTMRList (update_nth_vallist (Z.to_nat (Int.unsigned i)) tmrl 
  (lop_start tmri)) (set tmrls (Int.unsigned i) (hop_start tmr)) ** p.
Proof.
  intros.
  sep cancel p.
  unfold AOSTMRList in *.
  sep split in H4.
  sep auto. clear H4.
  unfold TMRList_P in *. 
  pose proof TMRList_P'_update_tmr tmrl tmrls tmri 0%nat (Z.to_nat (Int.unsigned i)) tmr start_tmrop H2.
  simpl in H4.
  erewrite Z2Nat.id in *.
  apply H4;eauto. 
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



(* Lemma OStimer_startProofPart3: forall p' 
tid i
(v' v'0: list val)
(v'7 v'8: val)
(v'9: list vallist)
(v'10: vallist)
(v'14: list vallist)
(v'15: vallist)
(v'18: TcbMod.map)
(v'27: TmrMod.map)
(v'32 v'47: list val)
(v'48: val),
Taskexeloc_P (v'32 ++
         Vint32 (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i) :: v'47)
        v'27 v' v'0 ->
length v'32 = length v'9 ->
length v'47 = length v'14 ->
V_OSTCBNext v'10 = Some v'48 ->
array_type_vallist_match Int32u v'32 ->
array_type_vallist_match Int32u v'47 ->
GoodLInvAsrt OSLInv ->
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
{{ <|| END Some (Vint32 Int.zero) ||>  **
  PV get_off_addr tid loc_off @ Int32u |-> Vint32 (($ __OSLoc_tmrstart_gettgcr<<ᵢ$ 4) +ᵢ  i) **
  PV get_off_addr tid flag_off @ Int8u |-r-> (V$ 1) **
  dllsegloc v'7 (Vptr tid) v'9 v'32 (fun vl : vallist => nth_val 0 vl) **
  dllsegloc v'48 Vnull v'14 v'47 (fun vl : vallist => nth_val 0 vl) **
  AOSTCBList v'7 v'8 v'9 (v'10 :: v'14) v'15 tid v'18 **
  CurTid tid **
  A_dom_lenv ((os_code_defs.timerid, Int32u) :: (err, Int32u) :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil) ** p'}}
  OSTCBCur′→OSTCBLoc =ₑ ′ 0
  {{ [| Taskexeloc_P  (v'32 ++ V$ 0 :: v'47)
 v'27 v' v'0 |] **
  <|| END Some (Vint32 Int.zero) ||>  **
  AOSTCBLoc v'7 (v'9 ++ v'10 :: v'14)  (v'32 ++ V$ 0 :: v'47) **
  AOSTCBList v'7 v'8 v'9 (v'10 :: v'14) v'15 tid v'18 **
  p_local OSLInv tid init_lg **
  A_dom_lenv
    ((os_code_defs.timerid, Int32u)
     :: (err, Int32u)
        :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil) ** p'}}.
Proof.
  intros.
  unfold AOSTCBList.
  unfold p_local at 2, LINV, OSLInv at 3, init_lg' at 2.
  hoare normal pre.
  pure intro.
  hoare remember (5::6::nil)%nat pre.
  hoare lifts (1::3::nil)%nat pre.
  eapply forward_rule2.
  eapply assign_rule.
  { instantiate (1:= Int32u). 
    eapply eq_int. tauto. }
  { subst H10;split.
   apply addrof_rv_to_lv.
   destruct tid. unfold get_off_addr.
   eapply symbolic_lemmas.struct_offset_rv;[
   symbolic_execution|
   reflexivity| | simpl;auto ].
   { unfold loc_off, field_offset. simpl. 
   clear. pauto. }
   symbolic_execution.  }
  { subst H10. intros.
    sep lift 11%nat in H10.
    apply sep_combine_lemmas.PV_separate_rw_frm in H10.
    unfold CurLINV,LINV, OSLInv.
    sep auto. 
    instantiate (1:= init_lg' Int.zero).
    unfold init_lg'. split;auto.
    unfold isflag;auto.  }

  subst H10.
  intros.
  apply astar_l_apure_intro.
  sep normal in H10.
  sep lift 12%nat in H10.
  apply sep_combine_lemmas.PV_separate_rw_frm in H10.
  sep lifts (5::7::9::1::10::nil)%nat in H10.
  apply dllsegloc_merge_locvl_frm in H10;auto.
  unfold AOSTCBLoc, p_local, LINV, OSLInv.
  sep auto;eauto.
  apply array_type_vallist_match_app. split;cbn;eauto.
  unfold isflag;split;auto.

  eapply Taskexeloc_P_zero_preserve;eauto.
Qed. *)