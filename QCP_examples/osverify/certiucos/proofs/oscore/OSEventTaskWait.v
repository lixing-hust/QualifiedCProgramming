(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion: void OS_EventTaskWait(OS_EVENT* pevent) **)
(**************************** Code:***********************************)
(*
Void ·OS_EventTaskWait·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

1       OSTCBCur′→OSTCBEventPtr =ₑ pevent′;ₛ
2       OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ 
                 OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
3       If (OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0)
        {
4           OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼OSTCBCur′→OSTCBBitY)
        };ₛ
5       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
               pevent′→OSEventTbl[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
6       pevent′→OSEventGrp =ₑ pevent′→OSEventGrp |ₑ OSTCBCur′→OSTCBBitY;ₛ
7       RETURN
}·. 
*)

(* Require Import ucert. *)
Require Import ucos_include.
Require Import OSETWaitPure.
Require Import Lia.

Open Scope code_scope.


Lemma OSEventTaskWait_proof:
    forall tid vl p r ll, 
      Some p =
      BuildPreI os_internal OS_EventTaskWait
                  vl ll OS_EventTaskWaitPre tid ->
      Some r =
      BuildRetI os_internal OS_EventTaskWait vl ll OS_EventTaskWaitPost tid ->
      exists t d1 d2 s,
        os_internal OS_EventTaskWait = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}} s {{Afalse}}. 
Proof. 
  init_spec.
  rename v'9 into ier.

  hoare unfold.
  hoare forward.
  hoare unfold.


  lets Hi3: range_ostcby H.
  destruct Hi3 as [Hi3 Hi2].
  assert (Z.to_nat (Int.unsigned i4) < length v'0)%nat.
  {
    rewrite H11.
    unfold OS_RDY_TBL_SIZE.
    
    apply z_le_7_imp_n;auto.
    lia.
  }
  
  lets Hx: array_int8u_nth_lt_len H2 H15.
  Import DeprecatedTactic.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)

(* ** ac:   Locate array_type_vallist_match_imp_rule_type_val_match. *)
  Import symbolic_lemmas.
  
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H11.
  unfold OS_RDY_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.
  rewrite H31.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  (*
  Focus 2.
  hoare lift 8%nat pre.
  apply backward_rule1 with Afalse.
  intros.

  sep remember (1::nil)%nat in H2.
  simpl in H2.
  mytac;auto.
  apply pfalse_rule.
   *)
  unfold AOSRdyGrp.
  hoare forward.
  (* simpl;splits;pauto. *)
  go.
  rewrite H31.

  rewrite <- update_nth_val_length_eq.
  rewrite H11.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  rewrite H31.
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H11.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H31.
  rewrite len_lt_update_get_eq.
  simpl.
(* ** ac:   Locate "$". *)
  Local Open Scope int_scope.
  destruct (Int.eq (x&ᵢInt.not i3) ($ 0));auto.
  rewrite H11.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  eapply forward_rule2.
  hoare forward.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.

  destruct v'1;tryfalse.
  auto.
  intros.
  eauto.
  apply disj_rule;pure intro.
  clear  H38 H39 H34.
  
  assert (Z.to_nat (Int.unsigned i4) < length v'4)%nat.
  rewrite H12.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H4 H34.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)
  rewrite H38.
  simpl.
  rtmatch_solve.
  go.
  (* simpl;splits;pauto. *)
  rewrite H38.
  simpl.
  auto.
  go.
  (* simpl;splits;pauto. *)

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  sep cancel p_local.
  sep cancel Astruct.
  sep cancel AEventData.
  simpl;auto.
 (* 2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto. *)
  splits; simpl; auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H31.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H38.
  simpl.
  auto.
  split;auto.
  rewrite H31.
  simpl.
  rewrite H31 in H35.
  rewrite len_lt_update_get_eq in H35.
  assert (Int.eq (x &ᵢInt.not i3) ($ 0) =true).
  clear -H35.
  simpl in H35.
  simpl.
  destruct (Int.eq (x &ᵢInt.not i3) ($ 0));tryfalse;auto.

  eapply event_wait_rl_tbl_grp';eauto.
  rewrite H11.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H31.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  apply int_lemma1;auto.
  split.
  rewrite H31.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H31.

  rewrite <- update_nth_val_length_eq.
  auto.
  splits; eauto.
  go.
  eauto.
  unfolds; simpl; eauto.
  eauto.
  rewrite H38.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rewrite H38.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.
  clear -H30. pure_auto.
  (*------------------------------*)
   
  assert (Z.to_nat (Int.unsigned i4) < length v'4)%nat.
  rewrite H12.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H4 H35.
  mytac.
  hoare forward.
  go.

  rewrite H36.
  simpl.
  rtmatch_solve.
  go.
  rewrite H36.
  simpl.
  auto.
  go.

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  sep cancel p_local.
  sep cancel Astruct.
  sep cancel AEventData.
  simpl;auto.
  splits; simpl; auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H31.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H36.
  simpl.
  auto.
  split;auto.
  rewrite H31.
  simpl.
  rewrite H31 in H34.
  rewrite len_lt_update_get_eq in H34.
  assert (Int.eq (x &ᵢInt.not i3) ($ 0) =false).
  clear -H34.
  simpl in H34.
  destruct (Int.eq (x &ᵢInt.not i3) ($ 0)). simpl in H34. destruct H34; tryfalse. auto.


  eapply event_wait_rl_tbl_grp'';eauto.
  rewrite H11.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H31.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  split.
  rewrite H31.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H31.

  rewrite <- update_nth_val_length_eq.
  auto.
  splits; eauto.
  go. eauto.
  unfolds; simpl; eauto.
  eauto.
  rewrite H36.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  eauto.
  apply array_type_vallist_match_hold;auto.
  rewrite H36.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.
  clear -H30. pure_auto.
Qed.
