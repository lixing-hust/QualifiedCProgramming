Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.

Open Scope int_scope.

Lemma OStimer_stopProofPart2 : forall 
  p' aop
  (tid: tid)
  (i : int32)
  (tmri: vallist)
  (Hmode: isGPtmr tmri = true),
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv tid init_lg **
 ((EX v0 : val, LV os_code_defs.timerid @ long |-> v0) **
  (EX v0 : val, LV err @ long |-> v0) **
  (EX v0 : val, LV ret @ long |-> v0) **
  (EX v0 : val, LV Timer_TGCR @ (long) ∗ |-> v0) ** Aemp) **
 Aie true **
 Ais nil ** Acs nil ** Aisr empisr ** (EX ier : language.ier, Aier ier)) **
A_dom_lenv
  ((os_code_defs.timerid, long)
   :: (err, long) :: (ret, long) :: (Timer_TGCR, (long) ∗) :: nil), Afalse|}|- tid
{{ <|| aop ||>  **
  LV Timer_TGCR @ (Int32u) ∗ |-> Vptr (timer_TGCR i) **
  AOSTMRNode i tmri **
  p_local OSLInv tid
    init_lg ** p'}} 
    ∗ Timer_TGCR ′ =ₑ ∗ Timer_TGCR ′ &ₑ ′ 4294967292 
  {{ <|| aop ||>  **
    LV Timer_TGCR @ (Int32u) ∗ |-> Vptr (timer_TGCR i) **
    AOSTMRNode i (lop_stop tmri) ** 
    p_local OSLInv tid
    init_lg ** p' }}.
Proof.
  intros.
  unfold AOSTMRNode. unfold lop_stop. rewrite Hmode.
  pure intro.
  hoare forward.
  unfold pre28bits in *.
  erewrite Int.and_assoc.
  assert (($ 4294967292&ᵢ$ 4294967280) = $ 4294967280) by mauto.
  rewrite H1.
  auto.
  cbn [ binaryop_nth_val intand_val].
  eauto.
Qed.
  
Lemma ostimer_absimp_tmrstop_succ_end:
forall i P sch tm tid tmrls prd em st tick om, 
    Int.ltu ($ 7) i = true ->
    Int.ltu i ($ 16) = true ->
    get tmrls (Int.unsigned i) = Some (gp_t prd em, st, tick, om) ->
    can_change_aop P -> 
    absinfer sch
     ( <||  tmrstop_succ (|Vint32 i :: nil|) ||>  **
      HTime tm **
      HCurTCB tid **
      HTMRList (Some tmrls) ** P)
      ( <|| END (Some (Vint32 (Int.zero)))  ||>  **
      HTime tm **
      HCurTCB tid **
      HTMRList (Some (set tmrls (Int.unsigned i) (hop_stop (gp_t prd em, st, tick, om))))  ** P ).
Proof.
  intros.
  tri_infer_prim; eexists;exgamma. 
  splits.
  simpl_subst_gamma.
  repeat hmstep_call_consturctor.
  instantiate (1:= (set O ostmrid
     (ostmr (Some (set tmrls (Int.unsigned i) (gp_t prd em, tm_idle, tick, om))))) ).
  instantiate (1:= O).
  2: try absinfer_side_condition_solver.
  3: apply map_join_emp.
  3: try solve [repeat rewrite jl_merge_emp; try apply map_join_emp].
  unfolds; try tri_exists_and_solver. 
  eapply tidsame_set. auto. 
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma ostimer_absimp_tmrstop_tmrnone :
    forall P sch i tm tid tmrls,  
      get tmrls (Int.unsigned i) = None ->
      can_change_aop P ->
              absinfer sch (<||
              tmrstop_tmrnone (|Vint32 i :: nil|) ?? 
              tmrstop_succ (|Vint32 i :: nil|) ||> **
              HTime tm **
              HCurTCB tid **
              HTMRList (Some tmrls) ** P)
      (<|| END (Some (Vint32 ($ -1))) ||>  ** 
      HTime tm **
      HCurTCB tid **
      HTMRList (Some tmrls) **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma ostimer_absimp_tmrstop_iderror :
    forall P sch aop i,  
      (Int.ltu ($ 7) i = false \/ Int.ltu i ($ 16) = false ) ->
      can_change_aop P ->
              absinfer sch (<||
              tmrstop_iderror (|Vint32 i :: nil|) ?? 
              aop ||>  ** P)
      (<|| END (Some (Vint32 ($ -1))) ||>  **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma OStimer_stopProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api OStimer_stop tmrstopapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OStimer_stop tmrstopapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OStimer_stop = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  hoare forward.
  hoare forward.
  (* If (os_code_defs.timerid ′ >ₑ ′ 7 &&ₑ ′ 16 >ₑ os_code_defs.timerid ′) *)
  hoare forward;pauto. 
  - instantiate (1:= 
  <|| END (Some (Vint32 ($ -1))) ||>  **
         Aisr empisr **
         Aie true **
         Ais nil **
         Acs nil **
         Aier v'3 **
         p_local OSLInv tid init_lg **
         LV ret @ Int32u |-> (V$ 0) **
         LV err @ Int32u |-> (V$ 0) **
         LV Timer_TGCR @ (Int32u) ∗ |-> v'2 **
         LV os_code_defs.timerid @ Int32u |-> Vint32 i **
         A_dom_lenv
           ((os_code_defs.timerid, Int32u) :: (err, Int32u) :: (ret, Int32u) :: (Timer_TGCR, (Int32u) ∗) :: nil)). 
   (*branch : condition true *)
    pure intro.
    assert (Int.ltu ($ 7) i = true) by pauto.
    assert (Int.ltu i ($ 16) = true) by pauto.
    (* ENTER_CRITICAL;ₛ *)
    hoare forward prim.
    pure intro.
    rename v'19 into vpthattr.
    rename v'20 into vcspace.
    rename v'21 into v21. 
    rename v'22 into v22. 
    rename v'23 into v23. 
     
    hoare lift 15%nat pre.
    unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
    pure intro.
    assert ((Int.unsigned (i -ᵢ $ 8) = Int.unsigned i -  8)%Z).
    { simpl_intltbool. rewrite Int_unsigned_minus. 
      rewrite Int.unsigned_repr by (cbn;lia).
      auto.
      rewrite Int.unsigned_repr by (cbn;lia).
      lia.  }
    assert ((Int.unsigned (i -ᵢ $ 8) < 8)%Z).
    { simpl_intltbool.
      rewrite H12.
      lia. }
    assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'22) = true).
    { apply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match;eauto. 
      rewrite H12. lia. }
    remember (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'22) as used_i.
    destruct used_i;tryfalse.
    (*choose the second abs op*)
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply absinfer_choice2;eauto.
    can_change_aop_solver.
    can_change_aop_solver.
    (* get tmrls not None  abs op step : ASSERT *)
    destruct H8 as [[tmrls [H8_ ]] | ].
    2:{  subst v'23.
      hoare_abscsq_tmr1.
      apply noabs_oslinv.
      eapply tmr_absinfer_TMRnotERROR_abort.
      can_change_aop_solver.
      apply absabort_rule. }
    subst v'23.
    my_destruct H8.
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply tmr_absinfer_TMRnotERROR_cont.
    can_change_aop_solver.
    (* If (OS_timerid_used ′ [os_code_defs.timerid ′ − ′ 8] ==ₑ ′ 1) *)
    hoare forward;pauto.
    { rewrite <- Heqused_i. auto. }
    { rewrite <- Heqused_i.
      unfold val_eq. 
      destruct (Int.eq i0 ($ 1)); pauto. }
    + instantiate (1:= Afalse). 
    (*branch : tmrused condition true *) 
    pure intro.
    assert (Int.eq i0 ($1) = true).
    { rewrite <- Heqused_i in *.
      unfold val_eq in *. 
      destruct (Int.eq i0 ($ 1)); auto. }
    clear H17 H18 H19.
    apply Int_eq_dec in H20.
    subst i0.
    rename v'22 into tmrusedl.
    rename v'21 into utmrl.
    (* choose the second abs op*)
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply absinfer_choice2;eauto.
    can_change_aop_solver.
    can_change_aop_solver.
    (* Timer_TGCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 9 +ₑ (os_code_defs.timerid ′ ≪ ′ 14));ₛ *)
    hoare lifts (1::37::7::38::28::39::nil)%nat pre.
    eapply seq_rule.
    eapply timer_assign_timerregs_shl with (n:= 9%nat);eauto. lia.
    unfold tmrregsLists; cbn [nth].
    (* lift AOSTMRList' and get tmri properties *)
    hoare lifts (12::nil)%nat pre.
    eapply backward_rule1.
    eapply AOSTMRList_separate;eauto. 
    pure intro.
    rename v'21 into tmri.
    rewrite nth_error_app2 in H17 by (simpl_intltbool;lia).
    rewrite H7 in H17.
    assert (exists abstmr, IsGPtmr tmri abstmr = true /\ get x0 (Z.of_nat (Z.to_nat (Int.unsigned (i -ᵢ $ 8)))  + 8) = Some abstmr /\ TMRNode_P tmri abstmr ).
    { eapply RLH_TMRused_is1;eauto.
      { rewrite H12.
      assert ((Z.to_nat (Int.unsigned i - 8)) = (Z.to_nat (Int.unsigned i) - 8))%nat by (simpl_intltbool;lia).
      rewrite H19.
      eauto. }
      { unfold TMR_used.
        apply nth_val_nth_error.
        eapply nth_val'_imply_nth_val;eauto.
        lia. } }
    my_destruct H19.
    apply andb_true_iff in H19 as [? ?].
    (* ∗ Timer_TGCR ′ &= ′ 4294967292;ₛ *)
    hoare lifts (3::4::1::7::nil)%nat pre.
    hoare forward. 
    eapply OStimer_stopProofPart2;eauto.
    (* change abs op*)
    assert ((Z.of_nat (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) + 8) = Int.unsigned i).
    { rewrite H12. simpl_intltbool. lia. }
    rewrite H23 in H20;clear H23.
    destruct_tmr x1;[ | false].
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply ostimer_absimp_tmrstop_succ_end;eauto.
    eapply join_get_r;eauto.
    can_change_aop_solver.
    (* merge tmrlist *)
    hoare lifts (7::9::nil)%nat pre.
    eapply backward_rule1.
    eapply AOSTMRList_merge;eauto.
    erewrite update_nth_vallist_app2 by (simpl_intltbool;lia).
    (*EXIT_CRITICAL;ₛ*)
    hoare forward prim.
    trycancel.
    unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
    sep normal.
    sep pauto.
    { left.
      eexists.
      split;eauto.
      exists x (set x0 (Int.unsigned i) (hop_stop (gp_t t e, st, tk, om))).
      splits;auto.
      eapply join_set_r;eauto.
      eapply get_indom;eauto.
      rewrite H7.
      eapply RLH_TMRList_P_user_update_tmr with (lh := stop_tmrop);eauto.
      simpl_intltbool;lia. }
    { split;auto.
      rewrite length_update_nth_vallist. auto. }
    { auto. }
    go.
    (* RETURN ′ 0 *)
    hoare forward.
    + hoare forward.
      (*branch : tmrused condition end *) 
      pure intro.
      rewrite <- Heqused_i in H17.
      unfold val_eq in H17.
      assert (Int.eq i0 ($ 1) = false).
      { destruct (Int.eq i0 ($ 1));auto.
        simpl in H17. destruct H17;tryfalse. }
      clear H17.
      assert (nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'22 = Some (Vint32 i0)).
      { eapply nth_val'_imply_nth_val;eauto.
        lia.  }
      clear Heqused_i.
      assert (Vint32 i0 = V$ 0 \/ Vint32 i0 = V$ 1).
      { eapply Forall_forall with (x:= Vint32 i0) in H11. auto.
        eapply nth_val_In;eauto. }
      destruct H19;inversion H19;subst i0;tryfalse.
      rewrite H12 in H17.
      assert (~ indom x0 (Int.unsigned i)).
      { assert (Int.unsigned i = Z.of_nat (Z.to_nat (Int.unsigned i - 8)) + 8) by (simpl_intltbool; lia).
        rewrite H20.
        eapply RLH_TMRused_is0;eauto.
        lia.
        eapply nth_val_nth_error;eauto. }
      assert (~ indom x (Int.unsigned i)).
      { unfold indom,not;intro.
        destruct H21.
        assert (Int.unsigned i = Z.of_nat (Z.to_nat (Int.unsigned i))) by (simpl_intltbool;lia).
        rewrite H22 in H21.
        lets Hx : RLH_TMRList_P_sys_idrange H15 H21.
        simpl_intltbool. lia. }
      assert (get tmrls (Int.unsigned i) = None).
      { apply nindom_get in H20,H21.
        erewrite map_join_get_none''';eauto. }
      (* change abs op*)
      hoare_abscsq_tmr1.
      apply noabs_oslinv.
      eapply ostimer_absimp_tmrstop_tmrnone;eauto.
      can_change_aop_solver.
      (* EXIT_CRITICAL *)
      hoare forward prim.
      2: eauto.
      trycancel.
      unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
      sep pauto.
      { left. eexists. split;eauto. }
      go.
      sep auto.
  - 
    hoare forward.
    + hoare forward.
      hoare forward.
    + 
      pure intro.
    assert (Int.ltu ($ 7) i = false \/ Int.ltu i ($ 16) = false).
    { destruct (Int.ltu ($ 7) i);destruct (Int.ltu i ($ 16));auto.
      simpl in H. 
      assert (Int.ltu Int.zero Int.one = true ) by pauto.
      rewrite H0 in H.
      simpl in H.
      destruct H;tryfalse. }
    hoare forward.
    hoare abscsq.
    apply noabs_oslinv.
    eapply ostimer_absimp_tmrstop_iderror;auto.
    can_change_aop_solver.
    (* RETURN ′ (-1) *)
    hoare forward.
Qed.
    



     
    
    