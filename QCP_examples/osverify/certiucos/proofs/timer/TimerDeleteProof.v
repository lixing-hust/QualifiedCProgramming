Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.
Require Import TimerDeleteRules.


Open Scope code_scope.
(* timer delete  Proof *)
Open Scope int_scope.

Lemma tmrdelete_absinfer_iderror :
 forall P sch i aop, 
    can_change_aop P ->
    Int.ltu ($ 7) i = false \/ Int.ltu i ($ 16) = false ->
    absinfer sch (<||  tmrdel_iderror (|Vint32 i :: nil|) ?? 
                      aop  ||> ** P) 
    (<|| END (Some (Vint32 (Int.repr (Zneg xH)))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma ostimer_absimp_tmrdelete_tmrnone :
    forall P sch i tm tid tmrls,  
      get tmrls (Int.unsigned i) = None ->
      can_change_aop P ->
              absinfer sch (<||
             tmrdel_tmrnone (|Vint32 i :: nil|) ?? 
             tmrdel_succ (|Vint32 i :: nil|) ||> **
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

Lemma tmrdelete_absinfer_succ_end :
 forall P sch tmrid x1 tm tid tmrls tmrls', 
    can_change_aop P ->
    Int.ltu ($ 7) tmrid = true ->
    Int.ltu tmrid ($ 16) = true ->
    join (sig (Int.unsigned tmrid) x1) tmrls' tmrls ->
    absinfer sch (<|| tmrdel_succ (|Vint32 tmrid :: nil|) ||> **
    HTime tm **
    HCurTCB tid **
    HTMRList (Some tmrls) ** P) 
    (<|| END (Some (Vint32 ($ 0))) ||> **
    HTime tm **
    HCurTCB tid **
    HTMRList (Some tmrls') ** P ).
Proof.
  infer_solver 0%nat.
Qed. 

Lemma OStimer_deleteProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api OStimer_delete tmrdelapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OStimer_delete tmrdelapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OStimer_delete = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  hoare forward.
  hoare forward.
  (* If (os_code_defs.timerid ′ >ₑ ′ 7 &&ₑ ′ 16 >ₑ os_code_defs.timerid ′) *)
  hoare forward.
  1,2,3: pauto.
  - (* branch yes*)
    instantiate (1:= <|| END (Some (Vint32 ($ -1)) ) ||>  **
    LV ret @ Int32u |-> (V$ 0) **
    LV err @ Int32u |-> (V$ 0) **
    Aier v'2 **
    p_local OSLInv tid init_lg **
    LV os_code_defs.timerid @ Int32u |-> Vint32 i **
    Aie true **
    Ais nil **
    Acs nil **
    Aisr empisr **
    A_dom_lenv
      ((os_code_defs.timerid, Int32u) :: (err, Int32u) :: (ret, Int32u) :: nil) ).
    pure intro.
    assert ( Int.ltu ($ 7) i = true /\ Int.ltu i ($ 16) = true) as [? ?] by pauto.
    (* absop : choose sencod and third branch *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_choice2.
    3:{ intros s' Hs'. exact Hs'. }
    can_change_aop_solver.
    can_change_aop_solver.
    (* ENTER_CRITICAL;ₛ *)
    hoare normal pre; hoare_ex_intro.
    eapply seq_rule; [ hoare_forward_prim'
    | try hoare_invchange ].
    unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
    pure intro.
    rename v'18 into vpthattr.
    rename v'19 into vcspace.
    rename v'20 into v20. 
    rename v'21 into v21. 
    rename v'22 into v22. 
    
    rename v'23 into v'18. 
    rename v'24 into v'19. 
    rename v'25 into v'20. 
    rename v'26 into v'21. 
    rename v'27 into v'22. 
  

     (* abs op : ASSERT TMRnotERROR;; *)
    destruct H6 as [[tmrls [H6_ H6]] | H6].
    2:{ rewrite H6.
        hoare_abscsq_tmr1.
        apply noabs_oslinv.
        eapply tmr_absinfer_TMRnotERROR_abort.
        can_change_aop_solver.
        apply absabort_rule. }
    subst v'22.
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply tmr_absinfer_TMRnotERROR_cont.
    can_change_aop_solver.
    my_destruct H6.
    assert ((Int.unsigned (i -ᵢ $ 8) = Int.unsigned i -  8)%Z).
    { simpl_intltbool. rewrite Int_unsigned_minus. 
      rewrite Int.unsigned_repr by (cbn;lia).
      auto.
      rewrite Int.unsigned_repr by (cbn;lia).
      lia.  }
    assert ((Int.unsigned (i -ᵢ $ 8) < 8)%Z).
    { simpl_intltbool.
      rewrite H14.
      lia. }
    assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'21) = true).
    { apply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match;eauto. 
      rewrite H14. lia. }
    remember (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'21) as used_i.
    destruct used_i;tryfalse.
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
      rename v'21 into tmrusedl.
      rename v'19 into systmrl.
      rename v'20 into utmrl.
      (*choose the third abs op*)
      hoare abscsq.
      apply noabs_oslinv.
      eapply absinfer_choice2;eauto.
      can_change_aop_solver.
      can_change_aop_solver.
      (* lift AOSTMRList' and get tmri properties *)
      hoare lifts (8::nil)%nat pre.
      eapply backward_rule1.
      eapply AOSTMRList_separate;eauto. 
      pure intro.
      rename v'19 into tmri.
      rewrite nth_error_app2 in H17 by (simpl_intltbool;lia).
      rewrite H5 in H17.
      assert (exists abstmr, IsGPtmr tmri abstmr = true /\ get x0 (Z.of_nat (Z.to_nat (Int.unsigned (i -ᵢ $ 8)))  + 8) = Some abstmr /\ TMRNode_P tmri abstmr ).
      { eapply RLH_TMRused_is1;eauto.
        { rewrite H14.
        assert ((Z.to_nat (Int.unsigned i - 8)) = (Z.to_nat (Int.unsigned i) - 8))%nat by (simpl_intltbool;lia).
        rewrite H19.
        eauto. }
        { unfold TMR_used.
          apply nth_val_nth_error.
          eapply nth_val'_imply_nth_val;eauto.
          lia. } }
      my_destruct H19.
      apply andb_true_iff in H19 as [? ?].
      rewrite H14 in H20.
      assert ((Z.of_nat (Z.to_nat (Int.unsigned i - 8)) + 8) = Int.unsigned i) by (simpl_intltbool;lia).
      rewrite H23 in H20;clear H23.
      assert (exists x', join (sig (Int.unsigned i) x1) x' x0) as [? ?].
      { eapply map_join_get_sig;eauto. }
      assert (join (sig (Int.unsigned i) x1) (merge x2 x) tmrls).
      { eapply join_join_merge23_join;eauto.
        apply join_comm;auto. }
      (* absop : tmrdel_succ (|Vint32 tmrid :: nil|) *)
      hoare_abscsq_tmr1.
      apply noabs_oslinv.
      eapply tmrdelete_absinfer_succ_end;eauto.
      can_change_aop_solver.
      (* OSreset_timer (­ os_code_defs.timerid ′­);ₛ *)
      hoare lifts (1::30::31::32::33::34::22::9::29::39::nil)%nat pre.
      hoare_call_aempiser.
      { intros. sep destruct H25.
        exists init_lg.
        sep auto. }
      { intros. sep destruct H25.
      exists init_lg.
      sep auto. }

      inversion H26. 
      subst v'21 v'23.
      rename v'20 into tmrid.
      (* meger two cases in reset post into one *)
      hoare remember (9::nil)%nat pre.
      eapply backward_rule1.
      instantiate (1:= EX tmri', AOSTMRNode tmrid tmri' ** [|V_OSTGCR tmri' = Some (V$ 0)|] ** H25).
      intros s Hs.
      apply disj_split_star in Hs.
      destruct Hs.
      { exists (update_nth_val 7 (update_nth_val 8 tmri (V$ 0)) (V$ 0)).
        sep cancel H25.
        sep auto.
        unfold V_OSTGCR.
        eapply nth_upd_neqrev;[lia | ].
        unfold isGPtmr, V_OSTGCR in H19.
        destruct (nth_val 8 tmri) eqn:?;[ | discriminate].
        eapply update_nth;eauto.  }
      { exists (tmri).
        sep cancel H25.
        sep auto.  }
      subst H25.
      pure intro.
      rename v'19 into new_tmri.
      (* merge tmrlist *)
      hoare lifts (1::17::nil)%nat pre.
      eapply backward_rule1.
      eapply AOSTMRNode_imply_length_frm;eauto.
      pure intro.
      eapply backward_rule1.
      eapply AOSTMRList_merge;eauto.
      erewrite update_nth_vallist_app2 by (simpl_intltbool;lia).
      (* OS_timerid_used ′ [os_code_defs.timerid ′ − ′ 8] =ₑ ′ 0;ₛ *)
      hoare forward.
      rewrite H14.
      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      2: eauto.
      unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
      sep normal.
      sep eexists.
      trycancel.
      sep split.
      sep lifts (5::3::2::4::nil)%nat in H27. apply H27.
      { left. eexists. split;eauto.
        exists x x2.
        splits;auto.
        { apply join_comm.
          eapply join_merge_disj.
          eapply join_join_disj_r;eauto.
          apply join_comm;eauto. }
        rewrite H5.
        eapply RLH_TMRList_P_user_delete_tmr with (tmri := tmri);eauto. }
      { split;auto.
        rewrite length_update_nth_vallist. auto. }
      { splits;auto.
        eapply array_type_vallist_match_hold;eauto.
        lia.
        rewrite update_nth_val_len_eq;auto.
        eapply Forall_update_nth_val;eauto. }
      pauto.
      (* RETURN ′ 0 {{Afalse}} *)
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
      assert (nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'21 = Some (Vint32 i0)).
      { eapply nth_val'_imply_nth_val;eauto.
        lia.  }
      clear Heqused_i.
      assert (Vint32 i0 = V$ 0 \/ Vint32 i0 = V$ 1).
      { eapply Forall_forall with (x:= Vint32 i0) in H11. auto.
        eapply nth_val_In;eauto. }
      destruct H19;inversion H19;subst i0;tryfalse.
      rewrite H14 in H17.
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
        lets Hx : RLH_TMRList_P_sys_idrange H12 H21.
        simpl_intltbool. lia. }
      assert (get tmrls (Int.unsigned i) = None).
      { apply nindom_get in H20,H21.
        erewrite map_join_get_none''';eauto. }
      (* change abs op*)
      hoare_abscsq_tmr1.
      apply noabs_oslinv.
      eapply ostimer_absimp_tmrdelete_tmrnone;eauto.
      can_change_aop_solver.
      (* EXIT_CRITICAL *)
      hoare forward prim.
      2: eauto.
      unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
      sep normal.
      sep eexists.
      trycancel.
      sep pauto.
      { left. eexists. split;eauto.  }
      pauto.
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
    eapply tmrdelete_absinfer_iderror;eauto.
    can_change_aop_solver.
    hoare forward.
Qed.