Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.

Open Scope code_scope.

Open Scope int_scope.

(* Lemma Taskexeloc_P_update_midlle_preserve_getloaddr :
forall vl1 v vl2 tmrls crevl crevh i t0 t1 t o,
  Taskexeloc_P (vl1 ++ v :: vl2) tmrls crevl crevh ->
  get tmrls (Int.unsigned i) = Some (t0,t1,t,o) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_P (vl1 ++ (Vint32 (($ __OSLoc_tmrget_getloaddr<<ᵢ$ 4) +ᵢ  i)) :: vl2 ) tmrls crevl crevh.
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

(* Lemma Taskexeloc_P_update_midlle_preserve_gethiaddr :
forall vl1 v vl2 tmrls crevl crevh i t0 t1 t o,
  Taskexeloc_P (vl1 ++ v :: vl2) tmrls crevl crevh ->
  get tmrls (Int.unsigned i) = Some (t0,t1,t,o) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_P (vl1 ++ (Vint32 (($ __OSLoc_tmrget_gethiaddr<<ᵢ$ 4) +ᵢ  i)) :: vl2 ) tmrls crevl crevh.
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

(* Lemma Taskexeloc_P_update_midlle_preserve_getlo :
forall vl1 v vl2 tmrls vlow1 vlow2 vhighl1 vhighl2 i t0 t1 t om o,
  Taskexeloc_P (vl1 ++ v :: vl2) tmrls (vlow1 ++ V$ t :: vlow2) (vhighl1 ++ V$ t / Int.zwordsize :: vhighl2) ->
  length vlow1 = Z.to_nat (Int.unsigned i) ->
  length vhighl1 = Z.to_nat (Int.unsigned i) ->
  get tmrls (Int.unsigned i) = Some (t0,t1,t,om, o) ->
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  Taskexeloc_P (vl1 ++ (Vint32 (($ __OSLoc_tmrget_getlo<<ᵢ$ 4) +ᵢ  i)) :: vl2 ) tmrls (vlow1 ++ V$ t :: vlow2) (vhighl1 ++ V$ t / Int.zwordsize :: vhighl2).
Proof.
  induction vl1;intros.
  - simpl in *.
    destruct v;tryfalse.
    destruct H.
    split;auto.
    solve_ExeNodeP.
    split;eauto. 
    split.
    rewrite <-H0.
    apply nth_val_middle.
    rewrite <-H1.
    apply nth_val_middle.
  - simpl in *.
    destruct a;tryfalse.
    destruct H.
    split;auto.
    eapply IHvl1;eauto.
Qed. *)

(* Lemma Taskexeloc_P_eq___OSLoc_tmrget_getloaddr :
forall vl tmrls crevl crevh n i,
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_val' n vl = Vint32 (($ __OSLoc_tmrget_getloaddr<<ᵢ$ 4) +ᵢ  i)
  -> Taskexeloc_P vl tmrls crevl crevh -> (exists tmri, get tmrls  (Int.unsigned i) = Some tmri).
Proof.
  induction vl;intros.
  -  destruct n;cbn [nth_val' Taskexeloc_P] in *;tryfalse. 
  -  cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H2.
  destruct n;cbn [nth_val' ] in H1.
  + inversion H1. subst.
  apply Int_ltu_true_intrepr_l in H as H4;[ | clear;mauto].
  apply Int_ltu_true_intrepr_r in H0 as H5;[ | clear;mauto].
  simpl_ExeNodeP H4 H5 H2.
  auto.
  + eapply IHvl;eauto.
Qed. *)

(* Lemma Taskexeloc_P_eq___OSLoc_tmrget_gethiaddr :
forall vl tmrls crevl crevh n i,
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_val' n vl = Vint32 (($ __OSLoc_tmrget_gethiaddr<<ᵢ$ 4) +ᵢ  i)
  -> Taskexeloc_P vl tmrls crevl crevh -> (exists tmri, get tmrls  (Int.unsigned i) = Some tmri).
Proof.
  induction vl;intros.
  -  destruct n;cbn [nth_val' Taskexeloc_P] in *;tryfalse. 
  -  cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H2.
  destruct n;cbn [nth_val' ] in H1.
  + inversion H1. subst.
  apply Int_ltu_true_intrepr_l in H as H4;[ | clear;mauto].
  apply Int_ltu_true_intrepr_r in H0 as H5;[ | clear;mauto].
  simpl_ExeNodeP H4 H5 H2.
  auto.
  + eapply IHvl;eauto.
Qed. *)

(* Lemma Taskexeloc_P_eq___OSLoc_tmrget_getlo :
forall vl tmrls crevl crevh n i,
  Int.ltu ($ 7) i = true ->
  Int.ltu i ($ 16) = true ->
  nth_val' n vl = Vint32 (($ __OSLoc_tmrget_getlo<<ᵢ$ 4) +ᵢ  i)
  -> Taskexeloc_P vl tmrls crevl crevh -> 
  exists tmrp tmrs tmrtick om hd,
     get tmrls (Int.unsigned i) =
     Some (tmrp, tmrs, tmrtick, om, hd) /\
      nth_val (Z.to_nat (Int.unsigned i)) crevl =
      Some (V$ tmrtick) /\
      nth_val (Z.to_nat (Int.unsigned i)) crevh =
      Some (V$ tmrtick / Int.zwordsize).
Proof.
  induction vl;intros.
  -  destruct n;cbn [nth_val' Taskexeloc_P] in *;tryfalse. 
  -  cbn [Taskexeloc_P] in *.
  destruct a;tryfalse.
  destruct H2.
  destruct n;cbn [nth_val' ] in H1.
  + inversion H1. subst.
  apply Int_ltu_true_intrepr_l in H as H4;[ | clear;mauto].
  apply Int_ltu_true_intrepr_r in H0 as H5;[ | clear;mauto].
  simpl_ExeNodeP H4 H5 H2.
  auto.
  + eapply IHvl;eauto.
Qed. *)

(* abs rules *)

(* Lemma tmrgettime_absinfer_assert_abt :
  forall P sch i v1 v2 v3 v4 v5 s, 
  (Int.ltu ($ 7) i  = true) ->
  (Int.ltu i ($ 16) = true) ->
  get v5 (Int.unsigned i) = None ->
  can_change_aop P ->
            absinfer sch (<|| ASSERT tmr_ex (Vint32 i);; s ||>  ** 
            HTime v3 ** HCurTCB v4 ** HTMRList v5 ** P) 
            (<|| ABORT ||> ** 
            HTime v3 ** HCurTCB v4 ** HTMRList v5 **
             P).
Proof.
  intros.
  eapply absinfer_trans.
  2: eapply absinfer_seq_abt;[ | | intros s' Hs;exact Hs].
  2,3 : can_change_aop_solver.
  eapply absinfer_seq;can_change_aop_solver.
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | sep auto | ].
  intros.
  unfold tmr_ex, not.
  intros. 
  my_destruct H4.
  inverts H4.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  sep remember (5::nil)%nat in H3.
  simpl_sat H3.
  simpljoin1.
  cbn [getabst] in *.
  assert (get o ostmrid = Some (ostmr v5)).
  { eapply join_sig_get;eauto.  }
  rewrite H3 in H5.
  inverts H5.
  tryfalse.
Qed.

Lemma tmrgettime_absinfer_assert :
  forall P sch i v1 v2 v3 v4 v5 s tk tmr tmrst om hd, 
  (Int.ltu ($ 7) i  = true) ->
  (Int.ltu i ($ 16) = true) ->
  get v5 (Int.unsigned i) = Some (tmr, tmrst, tk, om, hd) ->
  can_change_aop P ->
            absinfer sch (<|| ASSERT tmr_ex (Vint32 i);; s ||>  ** 
            HTime v3 ** HCurTCB v4 ** HTMRList v5 ** P) 
            (<|| s ||> ** 
            HTime v3 ** HCurTCB v4 ** HTMRList v5 **
             P).
Proof.
  intros.
  eapply absinfer_trans.
  2: eapply absinfer_seq_end with (v:= None);[ | | intros s' Hs;exact Hs].
  2,3 : can_change_aop_solver.
  eapply absinfer_seq;can_change_aop_solver.
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | sep auto | ].
  intros.
  destruct s0 as [[[[[[? ? ] ? ] ? ] ? ] ?] ?]. 
  unfold tmr_ex.
  eexists.
  splits;eauto.
  do 2 eexists.
  splits;eauto.
  sep remember (5::nil)%nat in H3.
  simpl_sat H3.
  simpljoin1.
  cbn [getabst] in *.
  eapply join_sig_get;eauto.
Qed. *)
Lemma tmrgettime_absinfer_updatelow_abt:
    forall P sch i x2 x1 v3 v4 v5 v6 v7 v8 v9 tk tmr tmrst om, 
    (Int.ltu ($ 7) i  = true) ->
    (Int.ltu i ($ 16) = true) ->
    get v5 (Int.unsigned i) = Some (tmr, tmrst, tk, om) ->
    ~ In_heape_addrval v8 x2 Int32u  ->
    can_change_aop P ->
              absinfer sch (<|| tmrget_succ_update_low (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|);;
              tmrget_succ_update_high (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|) ||>  ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 ** HCoreHeap v7 v8 v9 ** P) 
              (<|| ABORT ||> ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 ** HCoreHeap v7 v8 v9 **
               P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q := 
  HTime v3 **
  HCurTCB v4 **
  HTMRList (Some v5) ** HClkRate v6 ** HCoreHeap v7 v8 v9 ** P).
  1,2: can_change_aop_solver.

  eapply absinfer_abt; try (eauto || can_change_aop_solver).
  unfolds;intros.
  eexists;exgamma.
  splits.
  {
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { eapply spec_prim_step_abt.
  2: apply map_join_emp.
  do 3 eexists.
  splits;eauto.
  exists v5 v7 v8 v9 tk tmr.  exists tmrst om.
  split.
  { sep remember (3::nil)%nat in H4.
    simpl_sat H4;simpljoin1.
    eapply join_sig_get;eauto. }
  split.
  { sep remember (5::nil)%nat in H4.
    simpl_sat H4;simpljoin1.
    eapply join_sig_get;eauto. }
  split;auto. }
  hmstep_call_consturctor. }
  sep auto.

  eapply absinfer_seq_abt.
  1,2:can_change_aop_solver.
  sep auto.
Qed.

Lemma tmrgettime_absinfer_succ_updatelow:
    forall P sch i x2 x1 v3 v4 v5 v6 v7 v9 cheape1 cheape2 cntlowv' tk tmr tmrst om, 
    (Int.ltu ($ 7) i  = true) ->
    (Int.ltu i ($ 16) = true) ->
    get v5 (Int.unsigned i) = Some (tmr, tmrst, tk, om) ->
    In_heape_addrval (cheape1 ++ (x2, Int32u, cntlowv')::cheape2) x2 Int32u ->
    can_change_aop P ->
              absinfer sch (<|| tmrget_succ_update_low (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|);;
              tmrget_succ_update_high (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|) ||>  ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  
              HCoreHeap v7 (cheape1 ++ (x2, Int32u, cntlowv')::cheape2) v9 ** P) 
              (<|| tmrget_succ_update_high (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|) ||> ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  
              HCoreHeap v7 (cheape1 ++ (x2, Int32u, Vint32 (Int.repr tk))::cheape2) v9 **
               P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:=
  HTime v3 **
  HCurTCB v4 **
  HTMRList (Some v5) ** HClkRate v6 **  
  HCoreHeap v7 (cheape1 ++ (x2, Int32u, V$ tk) :: cheape2) v9 ** P).
  1,2: can_change_aop_solver.
  eapply absinfer_prim.
  1,2: can_change_aop_solver.
  2:
  eapply absinfer_seq_end with (v:= Some (Vint32 (Int.repr 1)));
  [can_change_aop_solver | can_change_aop_solver | sep auto].

  unfolds;intros.
  eexists;exgamma.
  splits.
  { 
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { assert (get O oscoreheapid = Some (oscoreheap (v7,(cheape1 ++ (x2, Int32u, cntlowv') :: cheape2), v9))).
  { sep remember (5::nil)%nat in H4.
  simpl_sat H4;simpljoin1.
  eapply join_sig_get;eauto. }
    eapply spec_prim_step.
    4: eapply map_join_emp.
    unfold tmrget_succ_update_low.
    do 3 eexists.
    splits;eauto.
    do 8 eexists.
    splits;eauto.
    { sep remember (3::nil)%nat in H4.
      simpl_sat H4;simpljoin1.
      eapply join_sig_get;eauto.  }
    left.
    splits;eauto.
    eexists.
    instantiate (1:= cheape1 ++ (x2, Int32u, V$ tk) :: cheape2).
    splits;eauto.
    unfold update_heape_addrval.
    do 3 eexists;splits;eauto.
    eapply abst_get_set_eqdom;eauto.
    simpl;auto.
    eapply tidsame_set; auto.
    eapply map_join_emp. }
  hmstep_call_consturctor. }
  sep remember (1::6::nil)%nat in H4.
  sep remember (1::6::nil)%nat.
  rewrite <- HeqH5.
  destruct s as [[[[[? ?] ? ] ? ] ?] ?]. 
  simpl_sat H4;simpl_sat_goal.
  simpljoin1.
  cbn [getabsop gettaskst emptaskst] in *.
  simpljoin1.

  do 6 eexists.
  splits;eauto.
  instantiate (2:= empenv).
  eapply join_comm.
  eapply map_join_emp.
  instantiate (2:= empenv).
  eapply join_comm.
  eapply map_join_emp.
  cbn;splits;auto.
  unfold emposabst;auto.

  do 6 eexists.
  splits;eauto.
  eapply join_comm.
  eapply map_join_emp.

  eapply abs_join_sig_set_join;eauto.
  sep auto.
Qed.

Lemma tmrgettime_absinfer_updatehigh_abt:
    forall P sch i x2 x1 v3 v4 v5 v6 v7 v8 v9 tk tmr tmrst om, 
    (Int.ltu ($ 7) i  = true) ->
    (Int.ltu i ($ 16) = true) ->
    get v5 (Int.unsigned i) = Some (tmr, tmrst, tk, om) ->
    ~ In_heape_addrval v8 x1 Int32u  ->
    can_change_aop P ->
              absinfer sch (<|| 
              tmrget_succ_update_high (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|) ||>  ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  HCoreHeap v7 v8 v9 ** P) 
              (<|| ABORT ||> ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  HCoreHeap v7 v8 v9 **
               P).
Proof.
  intros.
  eapply absinfer_abt; try (eauto || can_change_aop_solver).
  unfolds;intros.
  eexists;exgamma.
  splits.
  {
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { eapply spec_prim_step_abt.
  2: apply map_join_emp.
  do 3 eexists.
  splits;eauto.
  exists v5 v7 v8 v9 tk tmr.
  exists tmrst om.
  split.
  { sep remember (3::nil)%nat in H4.
    simpl_sat H4;simpljoin1.
    eapply join_sig_get;eauto. }
  split.
  { sep remember (5::nil)%nat in H4.
    simpl_sat H4;simpljoin1.
    eapply join_sig_get;eauto. }
  split;auto. }
  hmstep_call_consturctor. }
  sep auto.
Qed.

Lemma tmrgettime_absinfer_succ_updatehigh:
    forall P sch i x2 x1 v3 v4 v5 v6 v7 v9 cheape1 cheape2 cntlowv' tk tmr tmrst om, 
    (Int.ltu ($ 7) i  = true) ->
    (Int.ltu i ($ 16) = true) ->
    get v5 (Int.unsigned i) = Some (tmr, tmrst, tk, om) ->
    In_heape_addrval (cheape1 ++ (x1, Int32u, cntlowv')::cheape2) x1 Int32u ->
    can_change_aop P ->
              absinfer sch (<|| 
              tmrget_succ_update_high (|Vint32 i :: Vptr x2 :: Vptr x1 :: nil|) ||>  ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  
              HCoreHeap v7 (cheape1 ++ (x1, Int32u, cntlowv')::cheape2) v9 ** P) 
              (<|| END (Some (Vint32 (Int.repr 0)))||> ** 
              HTime v3 ** HCurTCB v4 ** HTMRList (Some v5) **
              HClkRate v6 **  
              HCoreHeap v7 (cheape1 ++ (x1, Int32u, V$ tk / Int.modulus)::cheape2) v9 **
               P).
Proof.
  intros. 
  eapply absinfer_prim;
  [can_change_aop_solver | can_change_aop_solver | sep auto].

  unfolds;intros.
  eexists;exgamma.
  splits.
  { 
  simpl_subst_gamma.
  hmstep_call_consturctor.
  { assert (get O oscoreheapid = Some (oscoreheap (v7,(cheape1 ++ (x1, Int32u, cntlowv') :: cheape2), v9))).
  { sep remember (5::nil)%nat in H4.
  simpl_sat H4;simpljoin1.
  eapply join_sig_get;eauto. }
    eapply spec_prim_step.
    4: eapply map_join_emp.
    unfold tmrget_succ_update_low.
    do 3 eexists.
    splits;eauto.
    do 8 eexists.
    splits;eauto.
    { sep remember (3::nil)%nat in H4.
      simpl_sat H4;simpljoin1.
      eapply join_sig_get;eauto.  }
    left.
    splits;eauto.
    eexists.
    instantiate (1:= cheape1 ++ (x1, Int32u, V$ tk / Int.modulus) :: cheape2).
    splits;eauto.
    unfold update_heape_addrval.
    do 3 eexists;splits;eauto. 
    eapply abst_get_set_eqdom;eauto.
    simpl;auto.
    eapply tidsame_set; auto.
    eapply map_join_emp. }
  hmstep_call_consturctor. }
  sep remember (1::6::nil)%nat in H4.
  sep remember (1::6::nil)%nat.
  rewrite <- HeqH5.
  destruct s as [[[[[? ?] ? ] ? ] ?] ?]. 
  simpl_sat H4;simpl_sat_goal.
  simpljoin1.
  cbn [getabsop gettaskst emptaskst] in *.
  simpljoin1.

  do 6 eexists.
  splits;eauto.
  instantiate (2:= empenv).
  eapply join_comm.
  eapply map_join_emp.
  instantiate (2:= empenv).
  eapply join_comm.
  eapply map_join_emp.
  cbn;splits;auto.
  unfold emposabst;auto.

  do 6 eexists.
  splits;eauto.
  eapply join_comm.
  eapply map_join_emp.

  eapply abs_join_sig_set_join;eauto.
  sep auto.
Qed.

Lemma tmrgettime_absinfer_iderror :
 forall P sch aop x x0 i, 
    can_change_aop P ->
    Int.ltu ($ 7) i = false \/ Int.ltu i ($ 16) = false ->
    absinfer sch (<|| tmrget_iderror (|Vint32 i :: x0 :: x :: nil|)
        ?? aop ||> ** P) (<|| END (Some (Vint32 (Int.repr (Zneg xH)))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma tmrgettimeproof_part0: 
  forall P aop
  (tid: tid)
  (low_addr: addrval)
  (i: int32)
  (v'28: val) 
  (i_tmrl: vallist),
  {|OS_spec, GetHPrio, OSLInv, I,
fun x2 : option val =>
( <|| END x2 ||>  **
  p_local OSLInv tid init_lg **
  ((EX v : val, LV cnthigh @ (Int32u) ∗ |-> v) **
   (EX v : val, LV cntlow @ (Int32u) ∗ |-> v) **
   (EX v : val, LV os_code_defs.timerid @ Int32u |-> v) **
   (EX v : val, LV err @ Int32u |-> v) **
   (EX v : val, LV ret @ Int32u |-> v) **
   (EX v : val, LV TimerRegs_CNTLO @ (Int32u) ∗ |-> v) **
   (EX v : val, LV TimerRegs_CNTHI @ (Int32u) ∗ |-> v) ** Aemp) ** Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX ier : language.ier, Aier ier)) **
 A_dom_lenv
   ((cnthigh, (Int32u) ∗)
    :: (cntlow, (Int32u) ∗)
       :: (os_code_defs.timerid, Int32u)
          :: (err, Int32u)
             :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil), Afalse|}|- tid
{{ <|| aop ||>  **
    LV cntlow @ (Int32u) ∗ |-> Vptr low_addr **
    LV TimerRegs_CNTLO @ (Int32u) ∗ |-> Vptr (timer_CNTLO i) **
    PV low_addr @ Int32u |-> v'28 **
    AOSTMRNode i i_tmrl **
    p_local OSLInv tid init_lg **
    A_dom_lenv
      ((cnthigh, (Int32u) ∗)
      :: (cntlow, (Int32u) ∗)
          :: (os_code_defs.timerid, Int32u)
            :: (err, Int32u)
                :: (ret, Int32u)
                  :: (TimerRegs_CNTLO, (Int32u) ∗)
                      :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil) ** P }}
  ∗ cntlow ′ =ₑ ∗ TimerRegs_CNTLO ′
  {{ <|| aop ||>  **
    LV cntlow @ (Int32u) ∗ |-> Vptr low_addr **
    LV TimerRegs_CNTLO @ (Int32u) ∗ |-> Vptr (timer_CNTLO i) **
    PV low_addr @ Int32u |-> (V_OSCNTLO' i_tmrl) **
    AOSTMRNode i i_tmrl **
    p_local OSLInv tid init_lg **
    A_dom_lenv
    ((cnthigh, (Int32u) ∗)
     :: (cntlow, (Int32u) ∗)
        :: (os_code_defs.timerid, Int32u)
           :: (err, Int32u)
              :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil) ** P }}.
Proof.
  intros.
  unfold AOSTMRNode.
  pure intro.
  hoare forward.
Qed.

Lemma ostimer_absimp_tmrget_tmrnone :
    forall P sch i low_addr high_addr tm tid tmrls,  
      get tmrls (Int.unsigned i) = None ->
      can_change_aop P ->
              absinfer sch (<||
              tmrget_tmrnone (|Vint32 i :: Vptr low_addr :: Vptr high_addr :: nil|)
              ?? tmrget_succ_update_low (|Vint32 i :: Vptr low_addr :: Vptr high_addr :: nil|);;
                 tmrget_succ_update_high (|Vint32 i :: Vptr low_addr :: Vptr high_addr :: nil|) ||> **
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

Lemma tmrgettimeproof_part1: 
  forall P aop
  (tid: tid)
  (high_addr: addrval)
  (i: int32)
  (v'115: val) 
  (i_tmrl: vallist),
   {|OS_spec, GetHPrio, OSLInv, I,
fun x2 : option val =>
( <|| END x2 ||>  **
  p_local OSLInv tid init_lg **
  ((EX v : val, LV cnthigh @ (Int32u) ∗ |-> v) **
   (EX v : val, LV cntlow @ (Int32u) ∗ |-> v) **
   (EX v : val, LV os_code_defs.timerid @ Int32u |-> v) **
   (EX v : val, LV err @ Int32u |-> v) **
   (EX v : val, LV ret @ Int32u |-> v) **
   (EX v : val, LV TimerRegs_CNTLO @ (Int32u) ∗ |-> v) **
   (EX v : val, LV TimerRegs_CNTHI @ (Int32u) ∗ |-> v) ** Aemp) ** Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX ier : language.ier, Aier ier)) **
 A_dom_lenv
   ((cnthigh, (Int32u) ∗)
    :: (cntlow, (Int32u) ∗)
       :: (os_code_defs.timerid, Int32u)
          :: (err, Int32u)
             :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil), Afalse|}|- tid
{{  <|| aop ||>  **
    LV cnthigh @ (Int32u) ∗ |-> Vptr high_addr **
    LV TimerRegs_CNTHI @ (Int32u) ∗ |-> Vptr (timer_CNTHI i) **
    PV high_addr @ Int32u |-> v'115 **
    AOSTMRNode i i_tmrl **
    p_local OSLInv tid init_lg **
    A_dom_lenv
    ((cnthigh, (Int32u) ∗)
     :: (cntlow, (Int32u) ∗)
        :: (os_code_defs.timerid, Int32u)
           :: (err, Int32u)
              :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil)** P }}
  ∗ cnthigh ′ =ₑ ∗ TimerRegs_CNTHI ′
  {{ <|| aop ||>  **
    LV cnthigh @ (Int32u) ∗ |-> Vptr high_addr **
    LV TimerRegs_CNTHI @ (Int32u) ∗ |-> Vptr (timer_CNTHI i) **
    PV high_addr @ Int32u |-> (V_OSCNTHI' i_tmrl) **
    AOSTMRNode i i_tmrl **
    p_local OSLInv tid init_lg **
    A_dom_lenv
    ((cnthigh, (Int32u) ∗)
     :: (cntlow, (Int32u) ∗)
        :: (os_code_defs.timerid, Int32u)
           :: (err, Int32u)
              :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil)** P }}.
Proof.
  intros.
  unfold AOSTMRNode.
  pure intro.
  hoare forward.
Qed.