Require Import ucos_include.
Require Import Lia.

Require Import sem_lab.
Require Import evauxvar_lemmas.
Require Import ternary_assignment.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.

Lemma tcbllsegevaux_split3_merge: 
  forall vll1 vl vll2 head locmp ptrmp s tn ct evloc vmux vsem vq
  locmp1 ptrmp1 locmp2 ptrmp2 locmp' ptrmp' vn P,
  s |=      llsegevaux head (Vptr ct) vll1 locmp1 ptrmp1 V_OSTCBNext **
           evaux_node ct evloc vmux vsem vq ** 
           llsegevaux vn tn vll2 locmp2 ptrmp2 V_OSTCBNext ** P ->
    V_OSTCBNext vl = Some vn -> 
    join (sig ct evloc) locmp2 locmp' ->
    join (sig ct (vmux, vsem, vq)) ptrmp2 ptrmp' ->
    join locmp1 locmp' locmp ->
    join ptrmp1 ptrmp' ptrmp  ->
    s |= llsegevaux head tn (vll1 ++ vl :: vll2) locmp ptrmp V_OSTCBNext ** P.
Proof.
  intros.
  sep normal in H.
  sep destruct H.
  sep split in H.
  sep lifts (2::3::nil)%nat in H.
  eapply llsegevaux_merge_hd in H;eauto.
  sep lifts (2::nil)%nat in H.
  eapply llsegevaux_merge2_frm in H;eauto.
Qed.

Lemma SemPtr_assign_lv : forall 
r ri aop ls 
(p':asrt )
(tid: tid)
(x0: addrval)  p1 tcbl1 tcbcur tcbl2 tcbls  rtbl p2 locmp ptrmp
,
 symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
 symbolic_lemmas.var_notin_dom tmpsem ls = false ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  **
  tcbllsegevaux p1 (tcbl1 ++ tcbcur :: tcbl2) locmp ptrmp **
  AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls  **
  p_local OSLInv tid init_lg **
  LV tmpsem @ OS_EVENT ∗ |-> Vptr x0 **
  A_dom_lenv ls ** p' }} 
  OSTCBCur ′ → __OSTskSemPtr =ₑ tmpsem ′
{{  <|| aop ||>   **
  [| get locmp tid = Some (V$ os_code_defs.__EvLoc_normal) |] **
  [| get ptrmp tid = Some (Vnull, Vnull, Vnull) |] **
  tcbllsegevaux p1 (tcbl1 ++ tcbcur :: tcbl2) locmp (set ptrmp tid (Vnull, Vptr x0, Vnull) ) **
  AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls  **
  p_local OSLInv tid (logic_val  (Vint32 (Int.repr 1%Z)) ::
                    logic_val (Vint32 (Int.repr __EvLoc_normal)) ::
                    logic_val Vnull ::
                    logic_val (Vptr x0) ::
                    logic_val Vnull ::
                    nil) **
  LV tmpsem @ OS_EVENT ∗ |-> Vptr x0 **
  A_dom_lenv ls ** p' }}.
Proof.
  intros.
  pure intro.
  (* split llsegevaux *)
  hoare lifts (2::3::4::nil)%nat pre.
  eapply backward_rule1.
  { unfold tcbllsegevaux, init_lg.
    intros s HS.
    eapply tcbllsegevaux_split3_join2_frm'';eauto. }
  pure intro.
  unfold evaux_node ,p_local,  OSLInv at 2, LINV.
  pure intro.
  (* merge PV get_off_addr tid semptr_off *)
  hoare lifts (4::9::nil)%nat pre.
  eapply backward_rule1.
  { intros s HS.
    eapply read_only_merge_all in HS as [? ?].
    exact H17.
    destruct H15 as [ | [? ?]];subst;cbn;auto.
    cbn;auto.  }
  unfold  AOSTCBList.
  pure intro.
  inverts H1.
  (* OSTCBCur ′ .. __OSTskSemPtr =ₑ tmpsem ′ *)
  eapply forward_rule2.
  { hoare lift 5%nat pre.
    hoare name lift Aop pre. 
    eapply assign_rule'.
    { instantiate (1:= Tptr OS_EVENT).
      eapply eq_vptr.
      do 2 eexists;eauto. }
    { split.
    apply addrof_rv_to_lv. 
    destruct tid. unfold get_off_addr.
    eapply symbolic_lemmas.struct_offset_rv;[ |
    reflexivity| | ].
    { eapply symbolic_lemmas.addrof_deref_rv.
    sep lifts (17::4::nil)%nat in H1.
    eapply symbolic_lemmas.gvar_rv;eauto. }
    { unfold  field_offset. simpl. 
    clear. pauto. }
    { cbn;auto. }
    symbolic_execution.  }
    { intros.
    sep lift 18%nat in H1.
    apply sep_combine_lemmas.PV_separate_rw_frm in H1.
    unfold p_local, CurLINV,LINV, OSLInv.
    sep auto.
    splits;eauto.
    unfold isevptr, isptr;right;eexists;eauto. }
  }
  intros.
  assert (join (sig tid (Vnull, Vptr x0, Vnull)) v'2 (set v'4 tid (Vnull, Vptr x0, Vnull) )).
  { eapply join_sig_set;eauto.  }
  assert (join v'0 (set v'4 tid (Vnull, Vptr x0, Vnull) ) ((set ptrmp tid (Vnull, Vptr x0, Vnull) ))).
  {  eapply join_comm. 
     eapply join_set_set;eauto.
     eapply join_comm;auto. 
     eapply join_sig_get;eauto.
  }
  (* clear H4 H6.  *)

  sep normal. sep eexists.
  sep cancel Aop.
  do 2 sep cancel tcbdllseg.
  do 2 sep cancel Agvarmapsto.
  sep cancel CurTid.
  sep cancel Alvarmapsto.
  sep cancel A_dom_lenv.
  sep cancel p'.
  sep split;eauto.

  apply sep_combine_lemmas.PV_separate_rw_frm in H1.
  eapply tcbllsegevaux_split3_merge with (vsem := Vptr x0) ;eauto.
  unfold evaux_node, OSLInv.
  sep semiauto.
  splits;auto.
  unfold isevptr, isptr;right;eexists;eauto.

  eapply join_get_r;eauto.
  eapply join_sig_get;eauto.

  eapply join_get_r;eauto.
  eapply join_sig_get;eauto.
Qed.

Lemma SemPtr_assign_null : forall 
r ri aop ls 
(p':asrt )
(tid: tid)
(x0: addrval)  p1 tcbl1 tcbcur tcbl2 tcbls  rtbl p2 locmp ptrmp
,
symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
symbolic_lemmas.var_notin_dom tmpsem ls = false ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  **
  tcbllsegevaux p1 (tcbl1 ++ tcbcur :: tcbl2) locmp ptrmp **
  AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls  **
  p_local OSLInv tid (logic_val  (Vint32 (Int.repr 1%Z)) ::
                    logic_val (Vint32 (Int.repr __EvLoc_normal)) ::
                    logic_val Vnull ::
                    logic_val (Vptr x0) ::
                    logic_val Vnull ::
                    nil) **
  A_dom_lenv ls ** p' }} 
  OSTCBCur ′ → __OSTskSemPtr =ₑ NULL
{{  <|| aop ||>   **
  [| get ptrmp tid = Some (Vnull, Vptr x0, Vnull) |] **
  tcbllsegevaux p1 (tcbl1 ++ tcbcur :: tcbl2) locmp (set ptrmp tid (Vnull, Vnull, Vnull) ) **
  AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls  **
  p_local OSLInv tid init_lg **
  A_dom_lenv ls ** p' }}.
Proof.
  intros.
  pure intro.
  Close Scope code_scope.
  (* split llsegevaux *)
  hoare lifts (2::3::4::nil)%nat pre.
  eapply backward_rule1.
  { unfold tcbllsegevaux.
    intros s HS.
    eapply tcbllsegevaux_split3_join2_frm'';eauto. }
  pure intro.
  unfold evaux_node ,p_local,  OSLInv at 2, LINV.
  pure intro.
  (* merge PV get_off_addr tid semptr_off *)
  hoare lifts (4::9::nil)%nat pre.
  eapply backward_rule1.
  { intros s HS.
    eapply read_only_merge_all in HS as [? ?].
    exact H17.
    destruct H15 as [ | [? ?]];subst;cbn;auto.
    cbn;auto.  }
  unfold  AOSTCBList.
  pure intro.
  inverts H1.
  (* OSTCBCur ′ .. __OSTskSemPtr =ₑ NULL *)
  eapply forward_rule2.
  { hoare lift 5%nat pre.
    hoare name lift Aop pre. 
    eapply assign_rule'.
    { instantiate (1:= Tnull).
      eapply eq_tnull. left.
      exists (OS_EVENT). auto. }
    { split.
    apply addrof_rv_to_lv. 
    destruct tid. unfold get_off_addr.
    eapply symbolic_lemmas.struct_offset_rv;[ |
    reflexivity| | ].
    { eapply symbolic_lemmas.addrof_deref_rv.
    sep lifts (16::4::nil)%nat in H1.
    eapply symbolic_lemmas.gvar_rv;eauto. }
    { unfold  field_offset. simpl. 
    clear. pauto. }
    { cbn;auto. }
    symbolic_execution.  }
    { intros.
    sep lift 17%nat in H1.
    apply sep_combine_lemmas.PV_separate_rw_frm in H1.
    unfold p_local, CurLINV,LINV, OSLInv.
    sep auto.
    splits;eauto. }
    (* unfold isevptr, isptr;right;eexists;eauto. } *)
  }
  intros.
  assert (join (sig tid (Vnull, Vnull, Vnull)) v'2 (set v'4 tid (Vnull, Vnull, Vnull) )).
  { eapply join_sig_set;eauto.  }
  assert (join v'0 (set v'4 tid (Vnull, Vnull, Vnull) ) ((set ptrmp tid (Vnull, Vnull, Vnull) ))).
  {  eapply join_comm. 
     eapply join_set_set;eauto.
     eapply join_comm;auto. 
     eapply join_sig_get;eauto.
  }
  (* clear H4 H6.  *)

  sep normal. sep eexists.
  sep cancel Aop.
  do 2 sep cancel tcbdllseg.
  do 2 sep cancel Agvarmapsto.
  sep cancel CurTid.
  (* sep cancel Alvarmapsto. *)
  sep cancel A_dom_lenv.
  sep cancel p'.
  sep split;eauto.

  apply sep_combine_lemmas.PV_separate_rw_frm in H1.
  eapply tcbllsegevaux_split3_merge with (vsem := Vnull) ;eauto.
  unfold evaux_node, OSLInv.
  sep semiauto.
  splits;auto.
  
  eapply join_get_r;eauto.
  eapply join_sig_get;eauto.
Qed.