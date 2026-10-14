Require Import ifun_spec.
Require Import ucos_include.
Require Import OSETWaitPure.  
Require Import Lia.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma event_wait_rl_tbl_grp1:
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 v'6 x0 i i1,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'6 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'6 = Vint32 x0 ->
    RL_Tbl_Grp_P v'6 (Vint32 i) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'6 (Vint32 (Int.or x0 i2)))
      (Vint32 (Int.or i i1)).
Proof.
  introv Hrl Harr Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x < 64) as Hran by lia.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 i = Vint32 i) by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  split.
  split.
  intros.
  apply He1.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  
  lets Hc : math_and_zero Hran Hn H.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  lets Hc : math_and_zero Hran Hn H.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He1; auto.
  lets Hc : math_and_zero Hran Hn H.
  split.
  intros.
  apply He2.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He2; auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
  inverts Hins.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  split.
  split.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  lets Hf : math_prop_neq_zero Hran.
  tryfalse.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  apply math_prop_neq_zero2 in H0.
  tryfalse.
  auto.
  split.
  intros.
  apply int_ltu_true; auto.
  intros.
  rewrite math_prop_eq; auto.
  rewrite Int.and_idem.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
Qed.

Lemma isptr_zh :
  forall x, isptr x ->
            match x with
              | Vundef => false
              | Vnull => true
              | Vint32 _ => false
              | Vptr _ => true
            end = true.
Proof.
  intros.
  unfolds in H; destruct H.
  substs; auto.
  destruct H; substs; auto.
Qed.

Lemma OS_EventTaskPostWait_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_EventTaskPostWait
                  vl logicl OS_EventTaskPostWaitPre ct ->
      Some r =
      BuildRetI os_internal OS_EventTaskPostWait vl logicl OS_EventTaskPostWaitPost ct ->
      exists t d1 d2 s,
        os_internal OS_EventTaskPostWait = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  rename v'9 into vptr.
  rename v'10 into ier.
  hoare unfold.
  unfold AOSPostEventTbl.
  hoare forward.
  hoare forward. 
   apply isptr_zh;auto.
  hoare unfold.

  lets Hi4: range_ostcby H.
  destruct Hi4 as [Hi4 Hi3].
  assert (Z.to_nat (Int.unsigned i4) < length v'0)%nat.
  {
    rewrite H17.
    unfold OS_RDY_TBL_SIZE.
    apply z_le_7_imp_n;auto.
    lia.
  }
  
  lets Hx: array_int8u_nth_lt_len H4 H33.
  Import DeprecatedTactic.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)

(* ** ac:   Locate array_type_vallist_match_imp_rule_type_val_match. *)
  Import symbolic_lemmas.
  
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H17.
  unfold OS_RDY_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.
  rewrite H34.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  unfold AOSRdyGrp.
  hoare forward.
  (* simpl;splits;pauto. *)
  go.
  rewrite H34.

  rewrite <- update_nth_val_length_eq.
  rewrite H17.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  rewrite H34.
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H17.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H34.
  rewrite len_lt_update_get_eq.
  simpl.
(* ** ac:   Locate "$". *)
  Local Open Scope int_scope.
  destruct (Int.eq (x&ᵢInt.not i3) ($ 0));auto.
  rewrite H17.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  eapply forward_rule2.
  hoare forward.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.

  destruct v'1;tryfalse. (*  v'1 -> (Vint32 i6)*)
  auto.
  intros.
  apply H36.
  apply disj_rule;pure intro.
  clear  H42 H41 H40.
  
  assert (Z.to_nat (Int.unsigned i4) < length v'6)%nat.
  rewrite H8.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H3 H40.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)
  rewrite H41.
  simpl.
  rtmatch_solve.
  go.
  (* simpl;splits;pauto. *)
  rewrite H41.
  simpl.
  auto.
  go.
  (* simpl;splits;pauto. *)

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  (*  Return  *)
  hoare forward. 
  
  instantiate(2 :=(x12
            :: x11
               :: Vptr (v'14, Int.zero)
                  :: v'3
                     :: Vint32 i9
                        :: Vint32 i8 :: Vint32 x1 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: nil) %list). (* i7 -> i8 *)
  instantiate (2:=v'9).
  sep cancel 3%nat 4 %nat.
    instantiate (2:=(update_nth_val (Z.to_nat (Int.unsigned i4)) v'6
              (val_inj (or (nth_val' (Z.to_nat (Int.unsigned i4)) v'6) (Vint32 i3))))).
  instantiate (2:=v'12).
  sep cancel 2%nat 3 %nat.
  instantiate (2:=v'10).
  sep cancel 2%nat 2 %nat.
  sep pauto.
  
  simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H34.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H41.
  simpl.
  auto.
  split;auto.
  splits.
  rewrite H34.
  simpl.
  rewrite H34 in H37.
  rewrite len_lt_update_get_eq in H37.
  assert (Int.eq (x &ᵢInt.not i3) ($ 0) =true).
  clear -H37.
  simpl in H37.
  simpl.
  destruct (Int.eq (x &ᵢInt.not i3) ($ 0));tryfalse;auto.

  eapply event_wait_rl_tbl_grp';eauto.
  rewrite H17.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H34.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  apply int_lemma1;auto.
  split.
  rewrite H34.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H34.

  rewrite <- update_nth_val_length_eq.
  auto. 
  go.

  rewrite H41.
  assert (v'13 = Vint32 i).
  {
  clear -H11 H12.
  unfold V_OSPostEventGrp in H11.
  unfold nth_val in H11. apply TcbMod.option2val. auto.
  }
  subst v'13.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  auto.
  apply array_type_vallist_match_hold;auto.
  rewrite H41.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  instantiate (1:= Vint32 i0).
  auto.
  auto.
  auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  pauto. pauto. pauto. change Byte.max_unsigned with 255%Z.
  lets Hx : int_unsigned_or_prop' H27 H32. rewrite Int.or_commut in Hx.
  clear -Hx.  pure_auto. 

  (*------------------------------*)
   
  assert (Z.to_nat (Int.unsigned i4) < length v'6)%nat.
  rewrite H8.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H3 H38.
  mytac.
  hoare forward.
  go.

  rewrite H39.
  simpl.
  rtmatch_solve.
  go.
  rewrite H39.
  simpl.
  auto.
  go.

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
  instantiate (2:= 
        (x12
            :: x11
               :: Vptr (v'14, Int.zero)
                  ::  v'3
                     :: Vint32 i9
                        :: Vint32 i8 :: Vint32 x1 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: nil)%list ).  (* i7 -> i8 *)
  instantiate (2:= v'9).
  sep cancel 3%nat 4%nat.
  instantiate (2:= (update_nth_val (Z.to_nat (Int.unsigned i4)) v'6
              (val_inj (or (nth_val' (Z.to_nat (Int.unsigned i4)) v'6) (Vint32 i3))))).
  instantiate (2:= v'12).
  sep cancel 2%nat 3%nat.
  instantiate (2:= v'10).
  sep cancel 2%nat 2%nat.
  sep pauto.
  simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H34.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H39.
  simpl.
  auto.
  split;auto.
  rewrite H34.
  simpl.
  rewrite H34 in H37.
  rewrite len_lt_update_get_eq in H37.
  assert (Int.eq (x &ᵢInt.not i3) ($ 0) = false).
  clear -H37.
  simpl in H37.
  destruct H37.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i3) ($ 0));tryfalse;auto.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i3) ($ 0));tryfalse;auto.
  
  split.
  eapply event_wait_rl_tbl_grp'';eauto.

  eapply idle_in_rtbl_hold;eauto.
  rewrite H17.
  simpl;auto.
  rtmatch_solve.
  split.
  rewrite H34.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H34.

  rewrite <- update_nth_val_length_eq.
  auto.
  go.
  simpl.
  rewrite H39.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  assert (v'13=Vint32 i).
  {
  clear -H11 H12.
  unfold V_OSPostEventGrp in H11.
  unfold nth_val in H11. apply TcbMod.option2val. auto.
  }
  subst v'13.
  pauto.
  simpl;auto.
  simpl;auto.
  
  apply array_type_vallist_match_hold;auto.
  rewrite H39.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  instantiate (1:=(Vint32 i0)).
  auto.
  simpl;auto.
  simpl;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  pauto.
  pauto.
  pauto.
  change Byte.max_unsigned with 255%Z.
  lets Hx : int_unsigned_or_prop' H27 H32. rewrite Int.or_commut in Hx.
  clear -Hx.  pure_auto. 

Qed.