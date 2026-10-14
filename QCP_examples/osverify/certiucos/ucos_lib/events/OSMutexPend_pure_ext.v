(* Require Import oseventto_proof. *)
(* Require Import ucos_include. *)
Require Import OSMutex_common.
Require Import OSTimeTickPure.
(* Require Import mutex_pend_pure. *)
(* Require Import symbolic_lemmas. *)
Require Import Lia.
Require Import sem_lab.
Require Import OSQPostPure.
Require Import OSMutexPendPure1.
(* Require Import seplog_pattern_tacs. *)

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma mutpost_intlemma1: 
forall x, Int.unsigned x <= 255 ->  (Int.modu x ($ Byte.modulus)) = x.
Proof.
  intros.
  unfold Int.modu.
  unfold Byte.max_unsigned.
  unfold Byte.modulus.
  unfold Byte.wordsize.
  unfold Wordsize_8.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  fold Byte.modulus.
  rewrite <- Byte.unsigned_repr_eq.
  assert (0 <= Int.unsigned x <= Byte.max_unsigned).
  change (Byte.max_unsigned) with 255.
  int auto.
  eapply Byte.unsigned_repr in H0.
  rewrite H0.
  rewrite Int.repr_unsigned. auto.
Qed.

(* copy from sempend_pure_ext.v *)

Ltac mytac :=
  heat; jeauto2.

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl petbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
induction els1.
intros.
tryfalse.
induction els1.
unfold get_last_ptr.
simpl.
intros.
destruct a.
destruct p. (* new add *)
destruct head;
try inverts H1.
destruct (beq_addrval qid a); try tryfalse.
destruct (V_OSEventListPtr v0 ); try tryfalse. (* v -> v0 *)
destruct v2; try tryfalse. (* v1 -> v2 *)
destruct (beq_addrval qid a0) eqn: eq1.
apply beq_addrval_eq in eq1.
subst. auto.
destruct (V_OSEventListPtr osevent); try tryfalse.
destruct v2; try tryfalse.  (* v1 -> v2 *)
intros.
destruct a.
destruct p. (* new add *)
assert (Hn: (a0 :: els1) <> nil) by pauto.
eapply (Mbox_common.get_last_prop) in Hn.
erewrite Hn.
destruct a0.
destruct p. (* new add *)
eapply IHels1; try pauto;
clear IHels0 IHels1 Hn;
simpl in *;
destruct head; try tryfalse; try auto;
destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
destruct (V_OSEventListPtr v3); try auto; try tryfalse; (* v1 -> v3 *)
destruct (V_OSEventListPtr v0); try tryfalse;  (* v -> v0 *)
destruct v6; try tryfalse;  (* v4 -> v6 *)
destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma ecblist_p_decompose_new:
  forall l1 ll1 l2 ll2 head ecbls tcbls eptr curl ecbcurl,
    length l1 = length ll1 ->
    get_ectr (Vptr eptr) head l1  = None ->
    get_ectr (Vptr eptr) head (l1 ++ (curl :: nil))  = Some curl ->
    ECBList_P head Vnull
              (l1++ (curl :: nil) ++ l2) (ll1 ++ (ecbcurl :: nil) ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2,
      ECBList_P head (Vptr eptr) l1 ll1 ecbls1 tcbls /\
      ECBList_P (Vptr eptr) Vnull ((curl :: nil) ++ l2) ((ecbcurl :: nil) ++ ll2) ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls /\ 
      (get_last_ptr l1 = None \/ get_last_ptr l1 = Some (Vptr eptr)).
Proof.
introv Hl Hgptr1 Hgptr2 Hep.
assert (Hl1: l1 = nil \/ l1 <> nil) by tauto.
destruct Hl1.
subst l1.
assert (ll1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ll1.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
destruct (beq_addrval eptr x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse. (*v,v1 -> v0, v2 *)
apply beq_addrval_eq in eq1.
subst x.
do 2 eexists.
splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
apply EcbMod.map_join_comm.
apply EcbMod.map_join_emp.
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
do 2 eexists. splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
Qed.

(* end of copy *)

(* copy from os_mutexpost_spec_v1.v *)

Lemma RH_ECBlk_EIBlk_Mux_P_set_op
: forall absmuxinfob els pid tid pt w pip x y wl,
get els pid = Some (absmutexsem x y, wl) ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob els ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob
  (set els pid (absmutexsem pip (Some (tid, pt)), w)).
Proof.
intros.
funfold H0.
unfold RH_ECBlk_EIBlk_Mux_P.
(* split; *)intros.
(* rewrite EcbMod.set_sem in H2.
destruct (tidspec.beq pid eid) eqn: eq1.
eapply tidspec.beq_true_eq in eq1.
subst.
eapply H0;eauto.
eapply H0;eauto. *)
(* eapply H1 in H2; eauto. *)
eapply H0 in H2; eauto.
do 3 destruct H2.
rewrite EcbMod.set_sem.
destruct (tidspec.beq pid eid) eqn: eq1.
eauto.
eauto.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_remove_owner
: forall absmuxinfob els pid pip x y wl w,
get els pid = Some (absmutexsem x y, wl) ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob els ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob
  (set els pid (absmutexsem pip None, w)).
Proof.
intros.
funfold H0.
unfolds.
(* split; *)intros.
(* rewrite EcbMod.set_sem in H2.
destruct (tidspec.beq pid eid) eqn: eq1.
eapply tidspec.beq_true_eq in eq1.
subst.
eapply H0;eauto.
eapply H0;eauto.
eapply H1 in H2; eauto. *)
eapply H0 in H2; eauto.
do 3 destruct H2.
rewrite EcbMod.set_sem.
destruct (tidspec.beq pid eid) eqn: eq1.
eauto.
eauto.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_change_wl
: forall absmuxinfob els pid x y wl w,
get els pid = Some (absmutexsem x y, wl) ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob els ->
RH_ECBlk_EIBlk_Mux_P absmuxinfob
  (set els pid (absmutexsem x y, w)).
Proof.
intros.
destruct y.
destruct p.
eapply RH_ECBlk_EIBlk_Mux_P_set_op; eauto.
eapply RH_ECBlk_EIBlk_Mux_P_remove_owner;eauto.
Qed.

(* copy from sempend_pure_ext.v *)

Lemma TCBListP_head_in_tcb':
  forall tcbls tcur tcurl tcblist rtbl prio msg,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBMsg tcurl = Some msg ->
     exists st sus, TcbMod.get tcbls tcur = Some (prio, st, msg, sus).
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
funfold H4.
destruct x2.
destruct p.
destruct p.
 mytac.
unfold V_OSTCBPrio, V_OSTCBMsg in *.
rewrite H in H7. inverts H7.
rewrite H0 in H6. inverts H6.
unfold TcbJoin in H3.
unfold join in H3; unfold sig in H3; simpl in H3.
do 2 eexists.
eapply TcbMod.join_get_l.
eauto.
eapply TcbMod.get_a_sig_a.
apply CltEnvMod.beq_refl.
Qed.

Lemma get_tcb_stat_rdy
: forall tcur tcurl tcblist rtbl tcbls prio st msg,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
rename H6 into Hsus1; rename H10 into Hsus2;
rename H11 into H6; rename H12 into H10.
funfold H10.
rename H15 into Hrhl_postq.
funfold H4.
funfold  H10.
funfold H2.
destruct H1.
subst t;assert(RdyTCBblk tcurl rtbl p /\
     V_OSTCBStat tcurl = Some (V$ OS_STAT_RDY) /\
     V_OSTCBDly tcurl = Some (V$ 0)) by (eapply H2; eauto);
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac.
rewrite H30 in *;
rewrite H29;inverts H4;
split; try pauto.
destruct H34; auto.
destruct H1; subst t.
specialize (H10 _ _ _ (eq_refl _)).
destruct H10 as (t & eq & Hw & Hlt & Hst).
splits; eauto.
unfold V_OSTCBStat,V_OSTCBEventPtr in *;
mytac;
rewrite H30 in *;
inverts Hst;inverts H29.
destruct H34; eauto.
Qed.

(* new add *)
Lemma get_tcb_stat_rdy_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  (st = rdy \/ (exists wt, st = wait os_stat_time wt)) ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then ($ OS_STAT_SUSPEND) else ($ OS_STAT_RDY))) /\
  V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_rdy; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H6.
assert (Hst: V_OSTCBStat tcurl = Some (V$ OS_STAT_SUSPEND)).
{  destruct H10 as (Hrdy & Hwt).
   destruct H1; simpljoin; subst.
   eapply Hrdy; eauto.
   specialize (Hwt _ _ _ (eq_refl _)).
   simpljoin; auto.
 }
split; auto.
funfold H4.
unfold V_OSTCBEventPtr.
rewrite H20 in H22; inverts H22.
rewrite H21.
destruct H25; auto.
Qed.

Lemma prio_in_tbl_imp :
forall p rtbl,
0 <= Int.unsigned p < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
prio_in_tbl p rtbl -> 
~(prio_not_in_tbl p rtbl).
Proof.
introv Hr Harr Hlen Hp.
unfold prio_in_tbl, prio_not_in_tbl in *.
lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
tauto.
eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
eapply Classical_Pred_Type.ex_not_not_all; exists v.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 1<<ᵢ(p&ᵢ$ 7)).
eapply Hp; try eauto.
rewrite H1.
eapply math_prop_neq_zero2.
eauto.
Qed.

Lemma prio_not_in_tbl_imp :
forall p rtbl,
0 <= Int.unsigned p < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
prio_not_in_tbl p rtbl -> 
~(prio_in_tbl p rtbl).
Proof.
introv Hr Harr Hlen Hp.
unfold prio_in_tbl, prio_not_in_tbl in *.
lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
tauto.
eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
eapply Classical_Pred_Type.ex_not_not_all; exists v.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
eapply Himp.
split; try auto.
assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 0).
eapply Hp; try eauto.
rewrite H1.
apply not_eq_comm.
eapply math_prop_neq_zero2.
eauto.
Qed.

Lemma RL_TCBblk_P_hold_for_update :
forall tcurl,
RL_TCBblk_P tcurl ->
RL_TCBblk_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)).
Proof.
intros.
funfold H.
unfold RL_TCBblk_P.
unfold V_OSTCBX,V_OSTCBPrio,V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSTCBStat,V_OSTCBEventPtr in *.
repeat eexists; 
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try eauto.
Qed.

Lemma TCBList_P_hold_for_update_rdy' :
forall tcbls tcur tcurl tcblist rtbl prio st msg ptbl tcbls' tcbls'' head tcblist' vhold sus,
  0 <= Int.unsigned prio < 64 ->
  array_type_vallist_match char_t rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
V_OSTCBDly tcurl = Some (Vint32 Int.zero) ->
TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
R_PrioTbl_P ptbl tcbls'' vhold ->
TcbMod.join tcbls' tcbls tcbls'' ->
TCBList_P head tcblist' rtbl tcbls' ->
TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
TCBList_P (Vptr tcur) 
                      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
                       (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7)))))
                             )
(TcbMod.set tcbls tcur (prio, rdy, msg, false)).
Proof.
simpl TCBList_P.
intros.
destruct H7 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
destruct asbs'.
destruct p.
destruct p.
exists td' vv' tcblss' (prio, rdy, msg, false).
inverts Hveq'.
  unfold sig in *. unfold TcbMap in *.
assert (Heq1: (prio, st, msg, sus) = (p, t, m, s)).
eapply TcbMod.map_get_unique.
eauto.
eapply TcbMod.join_sig_get. eauto.
inverts Heq1.
lets Hex :   int_usigned_tcb_range H.
  destruct Hex as (He1 & He2).
  assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
    lets Hgrp: array_type_match_get_value He1' H0 H1.
    destruct Hgrp as [grp]. rename H7 into Hgrp.
splits; try auto.
unfold V_OSTCBNext in *;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
unfold TcbMod.join in *.
intros.
specialize Htcj' with (a:= a).
erewrite TcbMod.sig_sem in *.
rewrite TcbMod.set_sem in *.
pure_auto.
  Focus 2.
  eapply TCBList_P_rtbl_add_lemma_2; try pauto.
  auto with zarith.
  fold nat_of_Z.
  eapply TCBList_P_rtbl_add_simpl_version; try eauto.
  lets Hget: TcbMod.join_get_r H5 H3.
  lets Hjs: TcbMod.map_join_get_sig Hget.
destruct Hjs as [x'].
  apply TcbMod.map_join_comm in H5.
  apply TcbMod.map_join_comm in Htcj'.
  lets Hjoin: join_join_merge H5 Htcj'.
  apply TcbMod.map_join_comm in Hjoin.
  eapply TCBList_P_rtbl_add_lemma_1.
  eauto.
  apply TcbMod.map_join_comm.
  apply TcbMod.join_merge_disj.
  eapply TcbMod.join_join_disj_r. eauto. eauto.
  unfold TcbJoin.
  auto with jdb. 
  unfold TcbJoin.
  unfold join. unfold sig. unfold TcbMap. eauto.
  funfold H4. auto.
(*TCBNode_P *)
destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
unfold TCBNode_P.
unfold V_OSTCBMsg,V_OSTCBPrio in *.
splits;
try (eapply nth_upd_neqrev; try pauto);
try (eapply nth_upd_neqrev; try pauto).
apply RL_TCBblk_P_hold_for_update; auto.

    funfold Hrtsl'.
    lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
  rewrite Hgrp'.
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H2.
  lets Heq1: nth_upd_neq nq1 H2.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Heq2 in Hvp.
  inverts Hvp.   funfold Hrsl'.
  split. try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  (*new_add*)
  left.
  splits. eapply update_nth; eauto.
  eapply nth_upd_neqrev; eauto. exists m; eauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H2.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  eapply prio_in_tbl_orself.

  (* RLH_Suspend_P *)
  unfolds.
  split; introv Hwt Hst;
  eapply nth_upd_eq in Hst; inverts Hst.
 (* RHL_Suspend_P *)
  unfolds.
  split; introv Hst; inverts Hst.

  lets Hnotp: prio_notin_tbl_orself H19 Hgrp.

  unfolds.
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].

  unfolds.
  introv Hwt Hst.
  unfolds in Hwt.
  destruct Hwt as (Hp & Hf & Hdly).
  eapply nth_upd_neq in Hp; eauto.
  eapply nth_upd_neq in Hp; eauto.
  rewrite Hvp in Hp; inverts Hp.
  tryfalse.

  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hwt Hst; eapply nth_upd_eq in Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
  splits; try solve [unfolds; introv Hst; inverts Hst].
Qed.

(* end of copy *)

Lemma get_tcb_stat_mutex
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  wt <> Int.zero ->
  st = wait (os_stat_mutexsem sid) (Some wt) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
rename H5 into Hsus1; rename H10 into Hsus2;
rename H11 into H5; rename H12 into H10.
funfold H10.
funfold  H14.
specialize (H14 _ _ _ _ (eq_refl _)).
destruct H14 as (Ht & Hpr & Hst).
destruct Ht as (t & [(Heq & Hs) | Hnone]).
inverts Heq.
destruct Hs as [(Hn & Hw) | (He & Hr)].
funfold Hw. eauto.
inverts He; tryfalse.
destruct Hnone as (Hne & Hw).
inverts Hne.
Qed.

Lemma get_tcb_stat_mutex_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  wt <> Int.zero ->
  st = wait (os_stat_mutexsem sid) (Some wt) ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_MUTEX))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_mutex; eauto.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H12.
specialize (H22 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H22 as [ (t & Heq & Hwt) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_mutex_zero
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  wt = Int.zero ->
  st = wait (os_stat_mutexsem sid) (Some wt) ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
rename H5 into Hsus1; rename H9 into Hsus2;
rename H10 into H5; rename H11 into H9.
funfold H9.
funfold H13.
specialize (H13 _ _ _ _ (eq_refl _)).
simpljoin.
unfold RdyTCBblk in *.
destruct H13 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
inverts Heq.
destruct Hcase as [(Hnz & _) | (_ & Hz)]; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_mutex_zero_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, true) ->
  wt = Int.zero ->
  st = wait (os_stat_mutexsem sid) (Some wt) ->
  V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H11.
specialize (H21 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H21 as [ (t & Heq & Hwt) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_mutex_none
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_mutexsem sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold  H13.
specialize (H13 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
destruct H13 as [ (Hf & _) | (_ & Hwait)]; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_mutex_none_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_mutexsem sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_MUTEX))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_mutex_none; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
funfold H11.
specialize (H21 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H21 as [ (t & Heq & Hwt) | (Heq & Hwt)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma R_PrioTbl_Pend_lift':
  forall ptcb_addr v'38 x v'53 v'32 tcbls cur_prio ptcb_prio xm v'46 i ost cm sus sus' sus'' sus''',
    (length v'32 = 64)%nat -> (**side condition**)
    Int.unsigned cur_prio < 64 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned ptcb_prio < 64 ->
    (ptcb_addr,Int.zero) <> (v'38,Int.zero) ->
    prio_available (x>>ᵢ$ 8) tcbls ->
(*     (nth_val' (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) v'32) = (Vptr v'53) -> *)
    R_PrioTbl_P v'32 tcbls v'53 ->
    TcbMod.get tcbls (v'38, Int.zero) = Some (cur_prio, rdy, cm, sus) ->
    TcbMod.get tcbls (ptcb_addr, Int.zero) = Some (ptcb_prio, ost, xm, sus') ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                      (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) v'32 (Vptr v'53))
                      (Vptr (ptcb_addr, Int.zero)))
      (TcbMod.set
         (TcbMod.set tcbls (v'38, Int.zero)
                     (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, cm, sus''))
         (ptcb_addr, Int.zero) (x>>ᵢ$ 8, ost, xm, sus''')) v'53.
Proof.
  introv Hax Hcr Hx Hpt Hneq Hpip (* Hnth *) Hrp Hget1 Hget2.
  unfolds.
  splits.
  introv Hp Hnthx Hneqq.
  unfold get in *.
  simpl in *.
  unfolds in Hrp.
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  remember ( ∘(Int.unsigned prio)) as pm.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember (Z.to_nat (Int.unsigned ptcb_prio)) as px.
  assert (pm <> pn \/ pm = pn) as Hart by tauto.
  destruct Hart as [Hart1 | Hart2].
  lets Hres : nth_upd_neq  Hart1 Hnthx.
  assert (pm <> px \/ pm = px) as Harst by tauto.
  destruct Harst as [Harst1 | Harst2].
  lets Hres2 : nth_upd_neq  Harst1 Hres.
  lets Hasb : Hrp1 Hneqq; eauto.
  rewrite <- Heqpm; auto. 
  unfolds in Hrp3.
  assert ( tcbid = (ptcb_addr, Int.zero) \/ tcbid <>  (ptcb_addr, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  unfold get in *; simpl in *.
  rewrite Hgs in Hget2.
  inverts Hget2.
  rewrite Heqpx in Harst1.
  rewrite Heqpm in Harst1.
  clear - Harst1.
  unfold nat_of_Z in Harst1.
  tryfalse.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  assert ( tcbid =(v'38, Int.zero)\/ tcbid <> (v'38, Int.zero)) by tauto.
  destruct H0.
  subst tcbid.

  unfold get in *; simpl in *.
  rewrite Hget1 in Hgs.
  inverts Hgs.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.

  rewrite Harst2 in Hres.
  lets Heqs: nth_upd_eq  Hres.
  inverts Heqs ; tryfalse.
  rewrite Hart2 in Hnthx.
  lets Heqs: nth_upd_eq  Hnthx.
  inverts Heqs.
  rewrite Heqpm in Hart2.
  rewrite   Heqpn in Hart2.
  assert (prio = (x>>ᵢ$ 8) ).
  clear - Hart2 Hx Hp.
  unfold nat_of_Z in Hart2.
  lets Has : Z2Nat.inj Hart2.  
  clear.
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  rewrite H.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  
  introv Hgets .
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  assert ( tcbid =   (ptcb_addr, Int.zero) \/ tcbid <>  (ptcb_addr, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  unfold nat_of_Z.
  lets Hxs : Hrp2 Hget2.
  destruct Hxs as (Hxs1 & Hxs2).
  split; auto.
  assert (exists xx,  nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) v'32 (Vptr v'53)) =
                      Some xx).
  eapply nth_val_upd_ex; eauto.
  rewrite Hax.
  clear - Hx.
  remember ( (x>>ᵢ$ 8)) as px.
  clear Heqpx.
  mauto.
  destruct H.
(* ** ac:   Locate update_nth. *)
(*   Import pure_lib. *)
  eapply update_nth; eauto.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.neq_beq_false in Hgets; eauto.
  assert ( tcbid =   (v'38, Int.zero)\/ tcbid <>   (v'38, Int.zero)) by tauto.
  destruct H0.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  lets Hnsa : Hrp3 H Hget1 Hget2.
  lets Hxas : Hrp2 Hget1.
  destruct Hxas.
  split; auto.
  Open Scope code_scope.
  assert ( (∘(Int.unsigned prio) < length v'32)%nat).
  rewrite Hax.
  clear -Hcr.
  mauto.
(* ** ac:   Locate ">>ᵢ". *)
(*   Open Scope int_scope. *)
  assert (∘(Int.unsigned prio) =  (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) \/
          ∘(Int.unsigned prio) <>(Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) by tauto.
  destruct H3.
  unfold nat_of_Z in H3.
  eapply inline_bittblfunctions.z2n_int_eq in H3.
  subst prio.
  lets Hfalse: Hpip Hget1.
  rewrite Int.eq_true in Hfalse.
  tryfalse.
  eapply nth_upd_neqrev; eauto.
  assert ( ∘(Int.unsigned prio) <>  (Z.to_nat (Int.unsigned ptcb_prio))).
  unfold nat_of_Z.
  introv Hf.
  apply Hnsa.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  eapply nth_upd_neqrev; eauto.
  rewrite TcbMod.set_sem in Hgets.
  rewrite tidspec.neq_beq_false in Hgets; eauto.
  lets Hnsa : Hrp3 H0 Hgets Hget1 .
  lets Hnsaa :  Hrp3 H Hgets Hget2 .
  lets Hxasx : Hrp2 Hgets.
  destruct Hxasx.
  assert (∘(Int.unsigned prio) =  (Z.to_nat (Int.unsigned (x>>ᵢ$ 8))) \/
          ∘(Int.unsigned prio) <>(Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) by tauto.
  destruct H3.
  unfold nat_of_Z in H3.
  eapply inline_bittblfunctions.z2n_int_eq in H3.
  subst prio.
  lets Hfalse: Hpip Hgets.
  rewrite Int.eq_true in Hfalse.
  tryfalse.
  split; auto.
  eapply nth_upd_neqrev; eauto.
  assert ( ∘(Int.unsigned prio) <>  (Z.to_nat (Int.unsigned ptcb_prio))).
  unfold nat_of_Z.
  introv Hf.
  apply Hnsaa.
  lets Has : Z2Nat.inj Hf.  
  clear .
  int auto.
  clear.
  int auto.
  eapply unsigned_inj; eauto.
  eapply nth_upd_neqrev; eauto.

  unfolds.
  intros.
  unfolds in Hrp.
  destruct Hrp as (Hpr1 & Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert ( (ptcb_addr, Int.zero) <> tid \/(ptcb_addr, Int.zero) = tid ) by tauto.
  destruct H2.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.
  assert (  (v'38, Int.zero) <> tid \/   (v'38, Int.zero) = tid ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.

  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H4.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  assert (  (v'38, Int.zero) <> tid' \/   (v'38, Int.zero) = tid' ) by tauto.
  destruct H5.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  lets Hrxx : Hpr3 H0 Hget1; eauto.

  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert ( prio <> x>>ᵢ$ 8 \/  prio = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  subst prio.
  lets Hfalse: Hpip H0.
  rewrite Int.eq_true in Hfalse.
  tryfalse.

  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.
  rewrite H3 in H1.
  rewrite TcbMod.set_sem in H1.
  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H0.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite <- H3 in H.
  eauto.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert ( prio <> x>>ᵢ$ 8 \/  prio = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  subst prio.
  lets Hfalse: Hpip Hget1.
  rewrite Int.eq_true in Hfalse.
  tryfalse.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.

  assert ( (ptcb_addr, Int.zero) <> tid' \/(ptcb_addr, Int.zero) = tid' ) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  assert (  (v'38, Int.zero) <> tid' \/   (v'38, Int.zero) = tid' ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.

  assert ( prio' <> x>>ᵢ$ 8 \/  prio' = x>>ᵢ$ 8) by tauto.
  destruct H4; auto.
  subst prio'.
  lets Hfalse: Hpip H1.
  rewrite Int.eq_true in Hfalse.
  tryfalse.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.

  assert ( prio' <> x>>ᵢ$ 8 \/  prio' = x>>ᵢ$ 8) by tauto.
  destruct H1; auto.
  subst prio'.
  lets Hfalse: Hpip Hget1.
  rewrite Int.eq_true in Hfalse.
  tryfalse.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  tryfalse.
Qed.

Lemma RL_RTbl_PrioTbl_P_set_not_rdy:
  forall x vhold rtbl ptbl ptcb_addr ptcb_prio,
    0 <= Int.unsigned ptcb_prio < 64 ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    (ptcb_addr, Int.zero) <> vhold -> 
   prio_not_in_tbl ptcb_prio rtbl ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    RL_RTbl_PrioTbl_P rtbl
   (update_nth_val (Z.to_nat (Int.unsigned x))
       (update_nth_val (Z.to_nat (Int.unsigned ptcb_prio)) ptbl (Vptr vhold))
       (Vptr (ptcb_addr, Int.zero))) vhold.
Proof.
intros.
unfolds.
intros.
lets Hnth: H4 H5 H6.
destruct Hnth as (tid & Hnth & Hneq).
assert (Hx: Z.to_nat (Int.unsigned x) = Z.to_nat (Int.unsigned ptcb_prio) 
                        \/ Z.to_nat (Int.unsigned x) <> Z.to_nat (Int.unsigned ptcb_prio)) by tauto.
destruct Hx as [Hx | Hx].
eapply inline_bittblfunctions.z2n_int_eq in Hx.
assert (Hp: Z.to_nat (Int.unsigned p) = Z.to_nat (Int.unsigned x) 
                        \/ Z.to_nat (Int.unsigned p) <> Z.to_nat (Int.unsigned x)) by tauto.
destruct Hp as [Hp | Hp].
eapply inline_bittblfunctions.z2n_int_eq in Hp.
substs.
exists (ptcb_addr, Int.zero).
split;auto.
repeat try eapply update_nth; eauto.
substs.
exists tid.
split;auto.
repeat try eapply nth_upd_neqrev; eauto.
assert (Hp: Z.to_nat (Int.unsigned p) = Z.to_nat (Int.unsigned x) 
                        \/ Z.to_nat (Int.unsigned p) <> Z.to_nat (Int.unsigned x)) by tauto.
destruct Hp as [Hp | Hp].
eapply inline_bittblfunctions.z2n_int_eq in Hp.
substs.
exists (ptcb_addr, Int.zero).
split;auto.
eapply update_nth; eapply nth_upd_neqrev; eauto.
assert (Hp2: Z.to_nat (Int.unsigned p) = Z.to_nat (Int.unsigned ptcb_prio) 
                        \/ Z.to_nat (Int.unsigned p) <> Z.to_nat (Int.unsigned ptcb_prio)) by tauto.
destruct Hp2 as [Hp2 | Hp2].
eapply inline_bittblfunctions.z2n_int_eq in Hp2.
substs.
eapply prio_not_in_tbl_imp in H3; eauto.
tryfalse.
exists tid.
split;auto.
repeat try eapply nth_upd_neqrev; eauto.
Qed.

Require Import Mbox_common.

Lemma TCBList_P_tcb_block_hold_mutex':
  forall (ptcb : addrval) (v1 v2 v3 v4 v5 : val) (v6 : int32) 
         (v8 : val) (v9 v10 : int32) (v11 : val) (rtbl : vallist)
         (vl : list (list val)) (tcbls : TcbMod.map) (prio : int32)
         (st : taskstatus) (m : msg) (qid : addrval) (time ry : int32),
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: v3
                  :: v4
                  :: v5
                  :: Vint32 v6
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, false) ->
    prio_neq_cur tcbls ptcb prio ->
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    nth_val ∘(Int.unsigned v9) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: Vptr qid
                  :: m
                  :: Vint32 time
                  :: V$OS_STAT_MUTEX
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (ry&ᵢInt.not v10)))
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) (Some time), m, false)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_mutexsem qid) (Some time),m, false).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.  
  unfolds.
  simpl.
  auto.
  funfold H2.
  swallow.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  pauto. (* new add *)
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  (* new add *)
  split.
  unfolds.
  split; intros;
  inverts H0.
  split.
  unfolds.
  split; intros;
  inverts H.
  (* end of new add *)
  split.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds.
  intros.
  unfolds in H.
  mytac.
  simpl_hyp.
  eexists.
  eauto.
  unfolds.
  intros.
  inverts H.
  false.
  inverts H5.
  eapply prio_update_self_not_in in Hnth; eauto.
  
  splits; try solve [ unfolds; intros; inverts H0].

  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  unfolds; intros.
  inverts H.
  splits; eauto.
  eexists.
  left. splits; eauto. left.
   splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
  splits; try solve [ unfolds; intros; inverts H].
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
(* ** ac:   Locate update_rtbl_tcblist_hold. *)
  eapply OSTimeDlyPure.update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold_mutex_sus':
  forall (ptcb : addrval) (v1 v2 v3 v4 v5 : val) (v6 : int32) 
         (v8 : val) (v9 v10 : int32) (v11 : val) (rtbl : vallist)
         (vl : list (list val)) (tcbls : TcbMod.map) (prio : int32)
         (st : taskstatus) (m : msg) (qid : addrval) (time ry : int32) sus stat,
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: v3
                  :: v4
                  :: v5
                  :: Vint32 v6
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st, m, sus) ->
    prio_neq_cur tcbls ptcb prio ->
    st = rdy \/ (exists n, st = wait os_stat_time n) ->
    nth_val ∘(Int.unsigned v9) rtbl = Some (Vint32 ry) ->
    time <> Int.zero ->
    stat = (if sus then Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) else ($ OS_STAT_MUTEX))  ->
    TCBList_P (Vptr ptcb)
              ((v1
                  :: v2
                  :: Vptr qid
                  :: m
                  :: Vint32 time
                  :: Vint32 stat
                  :: Vint32 prio
                  :: v8 :: Vint32 v9 :: Vint32 v10 :: v11 :: nil) :: vl)
              (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (ry&ᵢInt.not v10)))
              (TcbMod.set tcbls ptcb (prio, wait (os_stat_mutexsem qid) (Some time), m, sus)).
Proof.
  introv  Htcb Htm Hst Hprio Hnth Hneq Hstat.
  destruct sus; subst.
  2: eapply TCBList_P_tcb_block_hold_mutex'; eauto.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait (os_stat_mutexsem qid) (Some time),m, true).
  splits; eauto.
  eapply tcbjoin_set; eauto.
{
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds in H;simpl in H; inverts H.
  unfolds.
  split.
  unfolds.
  simpl.
  auto.
  funfold H2.
  splits.
  auto.
  unfolds.
  do 6 eexists; splits; try unfolds; simpl; eauto.
  splits; eauto.
  pauto.
  eexists.
  splits.
  unfolds;simpl; eauto.
  introv Hf.
  destruct Hf as [Hf | Hf];
  inverts Hf.
  lets Hexa : tcbjoin_get H1 Htm.
  inverts Hexa.
  unfolds in H4.
  split.
  unfolds.
  intros.
  simpl_hyp.
  unfolds in H.
  destruct H.
  simpl_hyp.
  unfolds in H0.
  assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
  assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
  assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
         (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
            (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
           Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hr: H0 H H2 H5.
  rewrite Int.and_assoc in Hr.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut.
  rewrite Int.and_not_self.
  auto.
  rewrite H6  in Hr.
  rewrite Int.and_zero in Hr.
  assert ( $ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
  unfold Int.zero in Hr.
  tryfalse.
  split.
  unfolds.
  intros.
  inverts H.
  (* new add *)
  split.
  unfolds.
  split; intros;
  inverts H0.
  split.
  unfolds.
  split; intros;
  inverts H.
  (* end of new add *)
  split.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  splits; try solve [ unfolds; intros; inverts H0].
  unfolds; intros.
  unfolds in H.
  mytac.
  simpl_hyp.
  eexists.
  eexists.
  splits; eauto.
  unfolds.
  splits; try solve [ unfolds; intros; inverts H].
  splits; try solve [ unfolds; intros; inverts H].
  unfolds.
  intros.
  inverts H.
  splits; eauto.
  left. eexists.
  splits; eauto.
  unfolds; try splits; simpl; eauto.
  eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
  eapply prio_update_self_not_in; eauto.
}
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac; simpl_hyp.
  funfold H2.
  eapply OSTimeDlyPure.update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma tjoin_get_none_r :
 forall ma mb mc x a,
 TcbMod.get ma x = Some a ->
 TcbMod.join ma mb mc ->
 TcbMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (TcbMod.get ma x).
  destruct (TcbMod.get mb x).
  tryfalse.
  auto.
  destruct (TcbMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma tjoin_get_none_l :
 forall ma mb mc x a,
 TcbMod.get mb x = Some a ->
 TcbMod.join ma mb mc ->
 TcbMod.get ma x = None.
Proof.
  intros.
  apply TcbMod.map_join_comm in H0.
  eapply tjoin_get_none_r; eauto.
Qed.

Lemma TcbMod_get_join_sig_set:
forall  qls qid a qls1 b,
  TcbMod.join (TcbMod.sig qid b) qls1 qls ->
  TcbMod.get qls1 qid = None ->
  TcbMod.join (TcbMod.sig qid a) qls1 (TcbMod.set qls qid a).
Proof.
  intros.
  unfold TcbMod.join.
  intros.
  rewrite TcbMod.sig_sem.
  rewrite TcbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite TcbMod.beq_refl.
  rewrite H0. auto.
  eapply tidspec.neq_beq_false in H1.
  rewrite H1.
  destruct (TcbMod.get qls1 a0) eqn: eq2.
  lets Htg: TcbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (TcbMod.get qls a0 = TcbMod.get qls1 a0).
  eapply TcbMod.map_join_get_none; try eauto.
  rewrite TcbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma tcbls_l_mutexpend':
  forall prio_lift  ptcb_prio v'33 v'34 v'45 v'43 x11 xm i8 ptcb_tcby ptcb_bitx ptcb_bity 
                v'36 os_rdy_tbl tcbls_l v'32 tcbls_r tcbls ptcb_addr v0 x5 vhold sus,
    
    get_last_tcb_ptr v'34 v'33 = Some (Vptr (ptcb_addr,Int.zero)) -> (*added*)
(*     nth_val' (Z.to_nat (Int.unsigned prio_lift)) v'32 = Vptr vhold -> (*added*) *)
    prio_available prio_lift tcbls -> (* add *)
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls vhold ->
    Int.unsigned prio_lift < 64 -> 
    ptcb_prio <>  prio_lift->
    TcbMod.get tcbls_l (ptcb_addr, Int.zero) = Some (ptcb_prio, rdy, xm, sus) ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl = Vint32 v0 ->
    nth_val' (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
             (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                             (Vint32 (v0&ᵢInt.not ptcb_bitx))) = Vint32 x5 ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 ptcb_prio
                       :: Vint32 i8
                       :: Vint32 ptcb_tcby
                       :: Vint32 ptcb_bitx
                       :: 
                       Vint32 ptcb_bity :: nil)
                    :: v'36) os_rdy_tbl tcbls_l ->
    TCBList_P v'33
              (v'34 ++
                    (v'45
                       :: v'43
                       :: x11
                       :: xm
                       :: V$0
                       :: V$OS_STAT_RDY
                       :: Vint32 prio_lift
                       :: Vint32 (prio_lift&ᵢ$ 7)
                       :: Vint32 (prio_lift>>ᵢ$ 3)
                       :: Vint32 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(prio_lift>>ᵢ$ 3)) :: nil) :: v'36)
              (update_nth_val (Z.to_nat (Int.unsigned (prio_lift>>ᵢ$ 3)))
                              (update_nth_val (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl
                                              (Vint32 (v0&ᵢInt.not ptcb_bitx)))
                              (Vint32 (Int.or x5 ($ 1<<ᵢ(prio_lift&ᵢ$ 7)))))
              (TcbMod.set tcbls_l (ptcb_addr, Int.zero) (prio_lift, rdy, xm, sus)).
Proof.
  introv Hlast (* Hhold *) Hpip_unuse.
  intros.
  apply TCBList_P_Split in H6.
  simpljoin.
  simpl in H9.
  simpljoin.
  unfolds in H10;simpl in H10;inverts H10.
  eapply TCBList_P_Combine;eauto.
  instantiate (1:= TcbMod.set x1 (ptcb_addr, Int.zero) (prio_lift, rdy, xm, sus)).
  eapply TcbMod.join_set_r;eauto.
  unfolds.
  unfold OSQPostPure.get_last_tcb_ptr in H6.
  unfold get_last_tcb_ptr in Hlast.
  rewrite Hlast in H6;inverts H6.
  exists x6.
  eapply tcbjoin_get_a_my;eauto.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  introv Hget.
  eapply semacc_int_eq_false; rewrite Int.eq_sym.
  eapply Hpip_unuse.
  eapply TcbMod.join_get_l; eauto.
  eapply TcbMod.join_get_l; eauto.
  (* assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg),
            TcbMod.get tcbls_l tid = Some (p, s, m) -> p <> prio_lift).
  eapply vhold_not_get';eauto.
  intros.
  eapply H9;eauto.
  eapply TcbMod.join_get_l;eauto. *)
  destruct x6.
  destruct p as ((p&st)&m).
(*   Require Import Mbox_common. *)
  lets Hcp : H12.
  funfold Hcp.
  funfold H14.
  eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs:= x1) (tcs':=tcbls_l) (prio:=x);eauto.
  eapply tcbjoin_get_a_my;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
   eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  eapply TcbMod.join_get_l; eauto.
  eapply TcbMod.join_get_r; eauto.
  eapply TcbMod.join_sig_get; eauto.
   apply nth_val'2nth_val;auto.

  simpl.
  unfold OSQPostPure.get_last_tcb_ptr in H6.
  unfold get_last_tcb_ptr in Hlast.
  rewrite Hlast in H6;inverts H6.
  unfold V_OSTCBNext; simpl nth_val.
  do 4 eexists;splits;eauto.
  eapply tcbjoin_set_my;eauto.
(*   instantiate (1:= x4). *)
(*   instantiate (1:= (prio_lift, rdy, xm)). *)
(*   eapply tcbjoin_set_my;eauto. *)
  destruct x6.
  destruct p.
  destruct p.
    (* new add *)
  lets Hget: TcbMod.join_sig_get H11.
  eapply TcbMod.join_get_r in Hget; eauto.
  rewrite H3 in Hget; inverts Hget.
  assert (Hsus: s = false).
  { funfold H12.
     eapply oscore_common.tcb_stat_imp_sus_false with (stat:= $ OS_STAT_RDY); eauto.
  }
  subst s.
  (* end of new add *)
  unfolds in H12.
  mytac.
  unfolds in H10.
  mytac.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  unfolds.
  splits.
(*   mytac. *)
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds.
  do 6 eexists;splits.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  unfolds;simpl;auto.
  split;auto.
  clear;int auto.
  splits;auto.
  eexists;split;auto.
  unfolds;simpl;auto.
  unfolds in H12.
  mytac.
  rename H10 into Hsus1; rename H12 into Hsus2;
  rename H14 into H10; rename H15 into H12. (* new add *)
  unfolds.
  splits;unfolds;intros.
  unfolds in H14.
  simpljoin.
  simpl_vqm.
  splits.
  unfolds;simpl;auto.
  left. splits.
  unfolds;simpl;auto.
  eexists;auto.
  inverts H14.
  splits.
  2:unfolds;simpl;auto.
  2:unfolds;simpl;auto.
  unfolds.
  splits.
  unfolds;simpl;auto.
  eapply prio_in_tbl_orself;eauto.
  (* new add *)
  split; introv Hwt Hf; inverts Hf.
  split; introv Hf; inverts Hf.
  (* end of new add*)
  splits; try solve [unfolds; intros; inverts H15].
  unfolds;intros.
  unfolds in H14.
  simpljoin.
  simpl_vqm.
  assert (~prio_not_in_tbl prio
           (update_nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3)))
                           (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 3))) os_rdy_tbl
                                           (Vint32 (v0&ᵢInt.not ($ 1<<ᵢ(x&ᵢ$ 7)))))
                           (Vint32 (Int.or x5 ($ 1<<ᵢ(prio&ᵢ$ 7)))))).
  eapply prio_notin_tbl_orself;eauto.
  apply nth_val'2nth_val;auto.
  false.
  splits; try solve [unfolds; intros; inverts H15].
  splits; try solve [unfolds; intros; inverts H15].
  splits; try solve [unfolds; introv Heq; inverts Heq].
  splits; try solve [unfolds; introv Heq; inverts Heq].

  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  introv Hget.
  eapply semacc_int_eq_false; rewrite Int.eq_sym.
  eapply Hpip_unuse.
  eapply TcbMod.join_get_l; eauto.
  eapply TcbMod.join_get_r; eauto.
  eapply TcbMod.join_get_r; eauto.
  destruct x6.
  destruct p.
  destruct p.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply Mbox_common.TCBList_P_tcb_block_hold' with (tcs:= TcbMod.sig (ptcb_addr, Int.zero) (p, t, m,s)) (tcs':=x1) (prio:=p);eauto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  rewrite TcbMod.sig_sem.
  rewrite tidspec.eq_beq_true;eauto.
  unfolds in H11.
  apply TcbMod.join_comm;auto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_r;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  clear -H10.
  unfolds in H10.
  simpljoin.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my in H11;eauto.
  eapply TcbMod.join_get_l;eauto.
  apply nth_val'2nth_val;auto.
Qed.

Lemma R_TCB_Status_P_change_prio:
forall pip tcbls rtbl ptbl vhold ot opt ost om sus v'38 v'36 x14 i8 x12,
  array_type_vallist_match Int8u rtbl ->
  length rtbl = ∘ OS_RDY_TBL_SIZE ->
  0 <= Int.unsigned pip < 64 ->
  prio_available pip tcbls ->
  RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
  R_PrioTbl_P ptbl tcbls vhold ->
  TcbMod.get tcbls ot = Some (opt,ost,om,sus) ->
  prio_not_in_tbl opt rtbl ->
  RL_TCBblk_P (v'38
              :: v'36
                 :: x14
                    :: om
                       :: Vint32 i8
                          :: Vint32 x12
                             :: Vint32 opt
                                :: Vint32 (opt&ᵢ$ 7)
                                   :: Vint32 (opt >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) ->
  R_TCB_Status_P
             (v'38
              :: v'36
                 :: x14
                    :: om
                       :: Vint32 i8
                          :: Vint32 x12
                             :: Vint32 opt
                                :: Vint32 (opt&ᵢ$ 7)
                                   :: Vint32 (opt >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil)
             rtbl (opt, ost, om, sus) ->
   R_TCB_Status_P
             (v'38
              :: v'36
                 :: x14
                    :: om
                       :: Vint32 i8
                          :: Vint32 x12
                             :: Vint32 pip
                                :: Vint32 (pip&ᵢ$ 7)
                                   :: Vint32 (pip >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(pip&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(pip >>ᵢ $ 3)) :: nil)
             rtbl (pip, ost, om, sus).
Proof.
introv Hmat Hlen Hpip_range Hpip_unuse Hrtbl Hptbl Hget Hopt_nin_rtbl Hrl_tcblk Hst.
 assert (Hopt_not_rdy: WaitTCBblk (v'38
     :: v'36
        :: x14
           :: om
              :: Vint32 i8
                 :: Vint32 x12
                    :: Vint32 opt
                       :: Vint32 (opt&ᵢ$ 7)
                          :: Vint32 (opt >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(opt&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(opt >>ᵢ $ 3)) :: nil) rtbl opt i8).
{ unfolds. splits; auto. }
assert(Hpip_nin_rtbl: ~(prio_in_tbl pip rtbl)).
{ unfolds. introv Hfalse.
   eapply Hrtbl in Hfalse; eauto.
   destruct Hfalse as (tid & Hnth & Hnvhold).
   eapply Hptbl in Hnth; eauto.
   destruct Hnth as (st & m & sus0 & Hfalse).
   eapply Hpip_unuse in Hfalse.
   rewrite Int.eq_true in Hfalse; tryfalse.
}
 assert (Hpip_not_rdy: WaitTCBblk (v'38
     :: v'36
        :: x14
           :: om
              :: Vint32 i8
                 :: Vint32 x12
                    :: Vint32 pip
                       :: Vint32 (pip&ᵢ$ 7)
                          :: Vint32 (pip >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(pip&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(pip >>ᵢ $ 3)) :: nil) rtbl pip i8).
{ unfolds. splits; auto.
   lets Hcase: prio_rtbl_dec Hpip_range Hmat Hlen.
   destruct Hcase; auto. tryfalse.
}
funfold Hst.
rename H1 into Hsus1; rename H2 into Hsus2;
rename H3 into H1; rename H4 into H2;
rename H5 into H3; rename H6 into H4. (* new add *)
funfold Hrl_tcblk.
unfolds.
splits; unfolds; intros.
funfold H5; tryfalse.
inverts H5.
assert(Hfalse:  (x, rdy, m, false) =  (x, rdy, m, false)) by auto.
eapply H0 in Hfalse.
mytac.
funfold H5.
eapply prio_in_tbl_imp in H8; eauto.
tryfalse.
(* new add *)
destruct Hsus1 as (Hsrdy & Hswt).
split; introv Hwt Hst; try introv Hlt;
destruct Hwt as (Hvp & Hnin & Hvt);
inverts Hvp; inverts Hvt.
eapply Hsrdy in Hst; eauto.
destruct Hst as (m & Heq); inverts Heq.
eauto.
eapply Hswt in Hst; eauto.
destruct Hst as (m & Heq); inverts Heq.
eauto.

destruct Hsus2 as (Hsrdy & Hswt).
split; introv Heq; inverts Heq.
specialize (Hsrdy _ _ (eq_refl _)).
destruct Hsrdy as (Hwt & Hst).
funfold Hwt.
split.
unfolds. splits; try solve [unfolds; simpl; auto].
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.
unfolds; simpl; auto.
specialize (Hswt _ _ _ (eq_refl _)).
destruct Hswt as (wt & Heq & Hwt & Hlt & Hst).
funfold Hwt.
eauto.
(* end of new add *)
destruct H1 as (Hwait_t & Hwait_sem & Hwait_sem_to & Hwait_q & Hwait_q_to & Hwait_mb  & Hwait_mb_to
& Hwait_mux & Hwait_mux_to & Hwait_postq & Hsus).
destruct Hsus as (Hss & Hsq & Hspq & Hsmb & Hsms & Hwait_port & Hwait_port_to & Hsport).
 (* add postq *)
splits. unfolds. introv Hwait Hst_eq.
inverts Hst_eq. destruct H18; eauto.
clear -Hwait_t Hwait Hopt_nin_rtbl.
unfolds in Hwait_t.
simpljoin1.
specialize (Hwait_t x i8) .
unfold WaitTCBblk, V_OSTCBPrio, V_OSTCBDly in Hwait_t. simpl in Hwait_t.
destruct Hwait_t;eauto.
inverts H0. inverts H1.
unfolds in Hwait.
mytac. inverts H0. inverts H2. split;eauto.

unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_sem.
specialize (Hwait_sem x i8 eid) .
destruct Hwait_sem; eauto.
unfolds in H1. mytac. inverts H1. inverts H7.
destruct H5 as [(Hne & Hst) | (He & Hst)]; inverts Hst; eexists; eauto.
unfolds; intros.
unfolds in Hwait_sem_to.
unfolds in H1. mytac. inverts H1. tryfalse.

unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_q.
specialize (Hwait_q x i8 eid) .
destruct Hwait_q; eauto.
unfolds in H1. mytac. inverts H1. inverts H7.
destruct H5 as [(Hne & Hst) | (He & Hst)]; inverts Hst; eexists; eauto.
unfolds; intros.
unfolds in Hwait_q_to.
unfolds in H1. mytac. inverts H1. tryfalse.

unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_mb.
specialize (Hwait_mb x i8 eid) .
destruct Hwait_mb; eauto.
unfolds in H1. mytac. inverts H1. inverts H7.
destruct H5 as [(Hne & Hst) | (He & Hst)]; inverts Hst; eexists; eauto.
unfolds; intros.
unfolds in Hwait_mb_to.
unfolds in H1. mytac. inverts H1. tryfalse.
split.
unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_mux.
specialize (Hwait_mux x i8 eid) .
destruct Hwait_mux; eauto.
unfolds in H1. mytac. inverts H1. inverts H7.
destruct H5 as [(Hne & Hst) | (He & Hst)]; inverts Hst; eexists; eauto.
split.
unfolds; intros.
unfolds in Hwait_mux_to.
unfolds in H1. mytac. inverts H1. tryfalse.
split.
unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_postq.
specialize (Hwait_postq x i8 eid) .
destruct Hwait_postq; eauto.
unfolds in H1. mytac. inverts H1. inverts H6. inverts H8.
splits; eauto.
(* new add about suspend *)
splits.
unfolds; introv Hwt Hst Hptr;
eapply Hss in Hptr; eauto;
funfold Hwt;
eauto.
unfolds; introv Hwt Hst Hptr;
eapply Hsq in Hptr; eauto;
funfold Hwt;
eauto.
unfolds; introv Hwt Hst Hptr;
eapply Hspq in Hptr; eauto;
funfold Hwt;
eauto.
unfolds; introv Hwt Hst Hptr;
eapply Hsmb in Hptr; eauto;
funfold Hwt;
eauto.
unfolds; introv Hwt Hst Hptr;
eapply Hsms in Hptr; eauto;
funfold Hwt;
eauto.
(* new add *)
unfolds; intros. inverts H5. inverts H6.
unfolds in Hwait_port.
specialize (Hwait_port x i8 eid) .
destruct Hwait_port; eauto.
unfolds in H1. mytac. inverts H1. inverts H7.
destruct H5 as [(Hne & Hst) | (He & Hst)]; inverts Hst; eexists; eauto.
unfolds; intros.
unfolds in Hwait_port_to.
unfolds in H1. mytac. inverts H1. tryfalse.
unfolds; introv Hwt Hst Hptr;
eapply Hsport in Hptr; eauto;
funfold Hwt;
eauto.
(* end of new add *)
destruct H2 as (Hwait_t & Hwait_sem & Hwait_q & Hwait_mb & Hwait_mux & Hwait_postq & Hsus). (* add postq *)
destruct Hsus as (Hss & Hsq & Hspq & Hsmb & Hsms & Hwait_port & Hsport).
splits; try (unfolds; introv Heq; inverts Heq);
[ specialize (Hwait_t _ _ _ (eq_refl _)); destruct Hwait_t; eauto
 | specialize (Hwait_sem _ _ _ _ (eq_refl _)); destruct Hwait_sem; eauto
 | specialize (Hwait_q _ _ _ _(eq_refl _)); destruct Hwait_q; eauto
 | specialize (Hwait_mb _ _ _ _ (eq_refl _)); destruct Hwait_mb; eauto
 | specialize (Hwait_mux _ _ _ _ (eq_refl _)); destruct Hwait_mux; eauto
 | specialize (Hwait_postq _ _ _ _(eq_refl _)); destruct Hwait_postq; eauto
 | specialize (Hss _ _ _ _(eq_refl _)); destruct Hss; eauto
 | idtac
];
eexists; eauto.

destruct H2 as (He & Hw & Hlt & Hst);
unfolds in Hw;
simpljoin1;
splits; eauto;
unfolds; splits; simpl; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.

destruct H2 as (t & [Hsome | Hnone]).
eexists ; eauto.
left.
destruct Hsome as (He & [(Heq & Hr) | (Hneq & Hw & Hdly)]).
unfolds in Hr. simpljoin1.
splits; eauto.
left; splits; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto. 
 false.
unfolds in Hw. simpljoin1. 
assert(~ prio_in_tbl x rtbl) by (eapply prio_not_in_tbl_imp; eauto). tryfalse.
destruct Hnone as (Hn & Hw). 
unfolds in Hw. simpljoin1. 
eexists. right; split; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.

destruct H2 as (t & [Hsome | Hnone]).
eexists ; eauto.
left.
destruct Hsome as (He & [(Heq & Hr) | (Hneq & Hw & Hdly)]).
unfolds in Hr. simpljoin1.
splits; eauto.
left; splits; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto. 
 false.
unfolds in Hw. simpljoin1. 
assert(~ prio_in_tbl x rtbl) by (eapply prio_not_in_tbl_imp; eauto). tryfalse.
destruct Hnone as (Hn & Hw). 
unfolds in Hw. simpljoin1. 
eexists. right; split; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.

destruct H2 as (t & [Hsome | Hnone]).
eexists ; eauto.
left.
destruct Hsome as (He & [(Heq & Hr) | (Hneq & Hw & Hdly)]).
unfolds in Hr. simpljoin1.
splits; eauto.
left; splits; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto. 
 false.
unfolds in Hw. simpljoin1. 
assert(~ prio_in_tbl x rtbl) by (eapply prio_not_in_tbl_imp; eauto). tryfalse.
destruct Hnone as (Hn & Hw). 
unfolds in Hw. simpljoin1. 
eexists. right; split; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.

destruct H2 as (t & [Hsome | Hnone]).
eexists ; eauto.
left.
destruct Hsome as (He & [(Heq & Hr) | (Hneq & Hw & Hdly)]).
unfolds in Hr. simpljoin1.
splits; eauto.
left; splits; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto. 
 false.
unfolds in Hw. simpljoin1. 
assert(~ prio_in_tbl x rtbl) by (eapply prio_not_in_tbl_imp; eauto). tryfalse.
destruct Hnone as (Hn & Hw). 
unfolds in Hw. simpljoin1. 
eexists. right; split; eauto.
unfolds; splits; simpl; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.

destruct H5 as (Hw & Hptr  & Hst).
unfolds in Hw.
simpljoin1. inverts H7.
inverts Hptr. inverts Hst. 
splits; unfolds; simpl; eauto.

(* new add *)
destruct H2 as [(t & Heq & Hwt (* & Hneq *)) | (Heq & Hwt)];
[left | right]; subst; funfold Hwt;
try solve[ repeat eexists; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto].

unfolds; introv Heq; inverts Heq;
specialize (Hsq _ _ _ _(eq_refl _)); destruct Hsq; eauto;
split; eauto;
destruct H2 as [(t & Heq & Hwt) | (Heq & Hwt)];
[left | right]; subst; funfold Hwt;
try solve[ repeat eexists; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto].

splits; unfolds; introv Heq; inverts Heq;
[ specialize (Hspq _ _ _ _ (eq_refl _)); destruct Hspq; eauto
 | specialize (Hsmb _ _ _ _ (eq_refl _)); destruct Hsmb; eauto
 | specialize (Hsms _ _ _ _ (eq_refl _)); destruct Hsms; eauto
 | (* specialize (Hwait_port _ _ _ _ (eq_refl _)); destruct Hwait_port; eauto *)
 | specialize (Hsport _ _ _ _ (eq_refl _)); destruct Hsport; eauto
];
try solve [
split; eauto;
destruct H2 as [(t & Heq & Hwt) | (Heq & Hwt)];
[left | right]; subst; funfold Hwt;
try solve[ repeat eexists; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto] ].
simpljoin.
splits; eauto.
funfold H5.
repeat eexists; eauto.
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto.


specialize (Hwait_port _ _ _ _ (eq_refl _)); destruct Hwait_port; eauto.
simpljoin1;
splits; eauto.
destruct H2 as [(t & Heq & Hsome) | (Heq & Hwt)];
[left | right]; subst.
destruct Hsome as [(Hneq & Hwt) | (Heq & Hr & Hdly)].
funfold Hwt;
try solve[ repeat eexists; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto].
false.
unfolds in Hr. simpljoin1.
assert(~ prio_in_tbl x rtbl) by (eapply prio_not_in_tbl_imp; eauto). tryfalse.
funfold Hwt;
try solve[ repeat eexists; eauto;
eapply not_prio_in_tbl_is_prio_not_in_tbl; eauto].
(* end of new add *)
Unshelve.
trivial. trivial. trivial. trivial.
Qed.

Lemma ecblist_p_mutexpend':
  forall v'57 v'69 v'38 v'46 x ptcb_addr wls x3 v'48 v'28 v'30 v'40 tcbls v'44 v'27 v'29 cur_prio v'66 v'65 v'68 v'64 i os_rdy_tbl x0 v'26 x12 i5 ptbl vhold om
               petbl pegrp petbl_addr sus sus',
    ((v'44 =  Vptr (v'46, Int.zero) /\ v'27 = nil)\/ get_last_ptr v'27 = Some (Vptr (v'46, Int.zero))) /\ (length v'27 = length v'29)-> (*added*)
    R_PrioTbl_P ptbl tcbls vhold -> (*added*)
    TCBNode_P
      (x0
         :: v'26
         :: x12
         :: om
         :: V$0
         :: V$OS_STAT_RDY
         :: Vint32 cur_prio
         :: Vint32 i5
         :: Vint32 v'64
         :: Vint32 v'65 :: Vint32 v'66 :: nil)
      os_rdy_tbl (cur_prio, rdy, om, sus) ->
    array_type_vallist_match Int8u v'57 ->
    RL_Tbl_Grp_P v'57 (Vint32 v'69) ->
    nth_val ∘(Int.unsigned v'64) v'57 = Some (Vint32 v'68) ->
    TcbMod.get tcbls (v'38, Int.zero) = Some (cur_prio, rdy, om, sus) ->
    EcbMod.get v'40 (v'46, Int.zero) =
    Some
      (absmutexsem (x>>ᵢ$ 8)
                   (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls) ->
    ECBList_P v'44 Vnull
              (v'27 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 v'69
                       :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: Vint32 pegrp :: petbl_addr :: nil,
                      v'57, petbl) :: nil) ++ v'28)
              (v'29 ++
                    (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
              v'40 tcbls ->
    ECBList_P v'44 Vnull
              (v'27 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 (Int.or v'69 v'66)
                       :: Vint32 x :: Vptr (ptcb_addr, Int.zero) :: x3 :: v'48 :: Vint32 pegrp :: petbl_addr :: nil,
                      update_nth_val ∘(Int.unsigned v'64) v'57 (Vint32 (Int.or v'68 v'65)), petbl)
                       :: nil) ++ v'28)
              (v'29 ++ (DMutex (Vint32 x) (Vptr (ptcb_addr, Int.zero)) :: nil) ++ v'30)
              (EcbMod.set v'40 (v'46, Int.zero)
                          (absmutexsem (x>>ᵢ$ 8)
                                       (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)),
                           (v'38, Int.zero) :: wls))
              (TcbMod.set tcbls (v'38, Int.zero)
                          (cur_prio, wait (os_stat_mutexsem (v'46, Int.zero)) i, om, sus')).
Proof.
  introv Hlink Hrptiotbl.
  destruct Hlink as (Hlink&Hleneq).
  intros.
  lets Hx:Mbox_common.ecblist_p_decompose Hleneq H5.
  mytac.
  assert ( x1 = Vptr (v'46, Int.zero)).
  {
    clear -H9 Hlink H6.
    destruct v'27.
    simpl in H6.
    mytac;auto.
    destruct Hlink;mytac;auto.
    unfolds in H.
    tryfalse.
    apply ECBList_last_val in H6;auto.
    mytac.
    destruct H9;destruct Hlink.
    destruct H2;tryfalse.
    rewrite H2 in H1; tryfalse.
    destruct H2;false.
    rewrite H2 in H1;inverts H1.
    auto.
  }
  
  subst x1.
  simpl in H7.
  mytac.
  inverts H7.
  destruct x5.
  assert ((e,w) = (absmutexsem (x>>ᵢ$ 8)
                               (Some (ptcb_addr, Int.zero, x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), wls)).
  {
    clear - H13 H8 H4. (* change H12 -> H13 *)
    apply ecbmod_joinsig_get in H13. (* change H12 -> H13 *)
    eapply EcbMod.join_get_r in H13;eauto. (* change H12 -> H13 *)
    rewrite H13 in H4;inverts H4;auto. (* change H12 -> H13 *)
  }

  inverts H7.
  eapply ecblist_p_compose;eauto.
  eapply EcbMod.join_set_r;eauto.
  unfolds.
  eexists.
  eapply ecbmod_joinsig_get;eauto.
  eapply ECBList_P_high_tcb_block_hold_mutex;eauto.

  eapply joinsig_join_getnone;eauto.
  simpl.
  eexists;mytac;swallow;eauto.
  clear H5.
  unfolds in H12;inverts H12. (* change H11 -> H12 *)

  eapply R_ECB_ETbl_P_high_tcb_block_hold_mutex; eauto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  clear -H.
  unfolds in H.
  mytac.
  unfolds in H1;mytac.
  simpl_vqm.
  auto.
  (* new add about petbl *)
  eapply Mbox_common.R_ECB_PETbl_P_high_tcb_block_hold; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
(*  do 3 eexists;splits;auto.
  unfolds;simpl;auto. *)
  eapply ecb_sig_join_sig'_set;eauto.
  simpl.

  unfolds in r.
  destructs r.
    
  swallow; auto.
  intros.
  tryfalse.

  eapply ECBList_P_high_tcb_block_hold_mutex;eauto.
  eapply joinsig_get_none;eauto.
Qed.

Lemma RH_TCBList_ECBList_P_pend_changeprio':
  forall tid tcbls ecbls pcur xm eid pip prio wl ost opt sus sus',
    R_Prio_No_Dup tcbls ->
    EcbMod.get ecbls eid = Some (absmutexsem pip (Some(tid, prio)), wl) ->
    TcbMod.get tcbls tid = Some (opt, ost, xm, sus)->
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls tid (pip,ost,xm, sus')) pcur.
Proof.
  introv Hidm He Ht (* Hpr *) (* Hneq *) Hrh.
  unfolds in Hrh.
  destruct Hrh as (Hrh1 & Hrh2 & Hrh3 & Hrh4 & Hrh5).
  unfolds.
  split.
  unfolds.
  splits.
  intros.
  apply Hrh1 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  (* new add about postq *)
   intros.
   apply Hrh1 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
    do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  (* end of new add *)
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh1; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh1 in H.
  eauto.
  (* new add about postq *)
   intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh1; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh1 in H.
  eauto.
  (* end of new add *)

  split.
  unfolds.
  split.
  intros.
  apply Hrh2 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh2; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh2 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh3 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh3; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh3 in H.
  eauto.

  split.
  unfolds.
  split.
  intros.
  apply Hrh4 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  split.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh4; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  destruct Hrh4 as (_ & Hrh4 & _ & _). (* new add *)
  eapply Hrh4 in H.
  eauto.

  split. (* new add *)
  unfolds.
  destruct Hrh4.
  destruct H0.
  destruct H1 as (H1 & _). (* new add *)
  unfolds in H1.
  intros.
  apply H1 in H2.
  destruct H2 as (H2 & Hin). (* new add *)
  split; auto. (* new add*)
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H3.
  subst.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.eq_beq_true ; eauto.
  rewrite  TcbMod.set_sem .
  rewrite tidspec.neq_beq_false ; eauto.

  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct Hrh4 as (_ & _ & How & Hrh4).
  destruct Hrh4 as (Hnone & Hsome (* & Hop  *)& Hdup).
   unfolds.
   splits; intros.
  assert (Hed: eid = eid0 \/ eid <> eid0) by tauto.
  destruct Hed. subst.
  unfold get in H. unfold EcbMap in H.
  rewrite He in H. inverts H.
   eapply OSTimeDlyPure.prio_available_hold_gen; try eapply Int.eq_false; eauto.

   rewrite TcbMod.set_sem in *.
   assert (Htd: tid = tid0 \/ tid <> tid0) by tauto.
  destruct Htd. subst.
  rewrite TcbMod.beq_refl in H0.
  inverts H0.
  assert (Hp2: opt = pip0 \/ opt <> pip0) by tauto.
  destruct Hp2. subst.
  eapply prio_available_hold_gen'; try eapply Int.eq_false; eauto.
  eapply OSTimeDlyPure.prio_available_hold_gen; try eapply Int.eq_false; eauto.
  lets Hf: tidspec.neq_beq_false H3.
  rewrite Hf in H0.
  assert (Hed: eid0 = eid \/ eid0 <> eid) by tauto.
  destruct Hed. subst.
  unfold get in H. unfold EcbMap in H.
  rewrite He in H. inverts H.
  tryfalse.
  eapply OSTimeDlyPure.prio_available_hold_gen; try eapply Int.eq_false; eauto.
(*   eapply Hop; eauto. *)
  eapply Hdup; eauto.

  split.
  intros.
  apply Hrh5 in H.
  mytac.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht; inverts Ht.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true ; eauto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false ; eauto.
  intros.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H0.
  subst.
  rewrite  TcbMod.set_sem  in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  eapply Hrh5; eauto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false  in H; auto.
  eapply Hrh5 in H.
  eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_mutex':
  forall (ecbls : EcbMod.map) (tcbls : TcbMod.map) 
         (pcur : tid) (qid : tidspec.A) (m : msg) cnt ot opt 
         (wl : waitset) (prio : priority) time sus sus',
    ot <> pcur ->
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (absmutexsem cnt (Some(ot,opt)), wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m, sus) ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmutexsem cnt (Some(ot,opt)), pcur :: wl))
                         (TcbMod.set tcbls pcur (prio, wait (os_stat_mutexsem qid) time, m, sus')) pcur.
Proof.
  introv Hot_neq Hr Ht He.
  unfolds in Hr.
  destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4 & Hr5).
  unfolds.
  splits.
  Focus 4.
{
  unfolds.
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  simpl in H0.
  destruct H0.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 (Some (ot, opt)), wl) /\ In tid wl) by eauto.
  apply Hr4 in H0.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  do 4 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmutexsem n1 n2, wls) /\ In tid wls) by eauto.
  apply Hr4 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  exists cnt.
  eexists.
  exists (tid::wl).
  splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
  simpl; left; auto.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr4 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 3 eexists; splits; eauto.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  simpl.
  right; auto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists; splits; eauto.
  unfolds.
  intros.
   assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H0.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
 assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H.
  subst.
  tryfalse. (* new add *)
   destruct Hr4.
  destruct H1.
  destruct H2 as (How & Howp). (* new add *)
  unfolds in How.
  apply How in Ht.
  mytac.
  split. (* new add *)
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
   rewrite not_in_cons; auto. (* new add *)
   rewrite EcbMod.set_sem in H.
   rewrite tidspec.neq_beq_false in H; auto.
   lets Hcp: Hr4.
   destruct Hcp as (_ & _ & How & Howp). (* new add *)
  unfolds in How. (* new add *)
  lets Hwl: How H. (* new add *)
  destruct Hwl as (Hex & Hwl). (* new add *)
   assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H1.
  subst.
  
  split; auto. (* new add *)
  rewrite TcbMod.set_sem ;
  rewrite tidspec.eq_beq_true; eauto.
destruct Hr4.
  destruct H3.
   split;auto. (* new add *)
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.

(* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
destruct Hr4 as (_ & _ & How & Howp). 
eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb'; eauto.
eapply rh_tcblist_ecblist_mutex_owner_set; eauto.
eapply OSTimeDlyPure.RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
}
  Unfocus.
  Focus 3.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid =Some (absmbox n, wls) /\ In tid wls) by eauto.
  apply Hr2 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr2 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
  Unfocus.
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid qwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  (* new add about postq *)
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid pqwaitset) by eauto.
  apply Hr3 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  (* end of new add *)
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  (* new add about postq *)
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr3 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do (* 3 *) 4 eexists; splits; eauto.
  (* end of new add *)
}
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
  apply Hr1 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr1 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists; splits; eauto.
}
{
  splits.
  intros.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite EcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  assert (EcbMod.get ecbls eid = Some (absport, wls) /\ In tid wls) by eauto.
  apply Hr5 in H2.
  mytac.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H3.
  subst.
  unfold get in *; simpl in *.
  rewrite H2 in He.
  inverts He. 
  do 3 eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
  intros.
  assert (pcur = tid \/ pcur <> tid) by tauto.
  destruct  H0.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  apply Hr5 in H.
  mytac.
  assert (qid  = eid \/ qid <> eid) by tauto.
  destruct H2.
  subst.
  unfold get in *; simpl in *.
  rewrite H in Ht.
  inverts Ht.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eexists; splits; eauto.
}

Qed.

Lemma low_stat_impl_high_stat_mutex
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    wt <> Int.zero ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_mutexsem sid) (Some wt), msg, false).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hne.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ &  Hrts & _).
  funfold Hrts.
  funfold H16.
  unfold WaitTCBblk in H16.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H16.
  rewrite H4,H5, H6, H7 in H16.
  rewrite H1.
  specialize (H16 prio wt sid).
  destruct H16; eauto. 
  destruct H as [Hneq | Heq].
  destruct Hneq as  (Hne' & Hst); inverts Hst; eexists; eauto.
  destruct Heq. inverts H; tryfalse.
Qed.

Lemma low_stat_impl_high_stat_mutex_sus
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    wt <> Int.zero ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_mutexsem sid) (Some wt), msg, true).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hne.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ &  Hrts & _).
  funfold Hrts.
  funfold H23.
  unfold WaitTCBblk in H23.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H23.
  rewrite H4,H5, H6, H7 in H23.
  rewrite H1.
  assert (exists m0 t_opt, (p, t, m, s) = (prio, wait (os_stat_mutexsem sid) t_opt, m0, true) /\
                                                     (wt = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None) \/
                                                       wt <> Int.zero /\ t_opt = Some wt)).
  eapply H23; try auto.
  destruct H as (m0 & t_opt & Heq & H).
  inverts Heq.
  destruct H as [ (Hf & _) | (_ & H)].
  subst.
  tryfalse.
  rewrite H.
  eauto.
Qed.

Lemma low_stat_impl_high_stat_mutex'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st msg sus,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     wt <> Int.zero ->
     st = wait (os_stat_mutexsem sid) (Some wt).
Proof.
intros.
  lets Hget : low_stat_impl_high_stat_mutex H H0 H1 H2 H3.
  lets Hget': Hget H4.
  clear Hget. destruct Hget'.
  eauto.
  rewrite H5 in H7.
  inverts H7.
  auto.
Qed.

Lemma low_stat_impl_high_stat_mutex_zero
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    wt = Int.zero ->
     exists msg,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_mutexsem sid) (Some wt), msg, false).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hne.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ & Hrts & _).
  funfold Hrts.
  funfold H17.
  unfold RdyTCBblk in H17.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H17.
  rewrite H4,H5, H7 in H17.
  rewrite H1.
  specialize (H17 prio sid).
  destruct H17; eauto. 
  inverts H. eauto.
Qed.

Lemma low_stat_impl_high_stat_mutex_zero_sus
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    wt = Int.zero ->
     exists msg t_opt,
       TcbMod.get tcbls tcur = Some (prio, wait (os_stat_mutexsem sid) t_opt, msg, true) /\
       (t_opt = (Some wt) \/ t_opt = None).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn Hne.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H9 as (_ & _ & _ & _ &  Hrts & _).
  funfold Hrts.
  funfold H23.
  unfold WaitTCBblk in H23.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in H23.
  rewrite H4,H5, H6, H7 in H23.
  rewrite H1.
  assert (exists m0 t_opt, (p, t, m, s) = (prio, wait (os_stat_mutexsem sid) t_opt, m0, true) /\
                                                     (Int.zero = Int.zero /\ (t_opt = Some Int.zero \/ t_opt = None) \/
                                                       Int.zero <> Int.zero /\ t_opt = Some Int.zero)).
  eapply H23; try auto.
  destruct H as (m0 & t_opt & Heq & H).
  inverts Heq.
  destruct H as [(_ & H) |  (Hf & _) ].
  eauto.
  tryfalse.
Qed.


Lemma low_stat_impl_high_stat_mutex_zero'
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st msg sus,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     prio_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBDly tcurl = Some (Vint32 wt) ->
     V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_MUTEX)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
     wt = Int.zero -> 
     st = wait (os_stat_mutexsem sid) (Some wt).
Proof.
intros.
  lets Hget : low_stat_impl_high_stat_mutex_zero H H0 H1 H2 H3.
  lets Hget': Hget H4.
  clear Hget. destruct Hget'.
  eauto.
  rewrite H5 in H7.
  inverts H7.
  auto.
Qed.

Lemma low_stat_impl_high_stat_neq_mutex
 : forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
          (rtbl : vallist) (tcbls : TcbMod.map) st prio msg,
     TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
     V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_MUTEX)) ->
     V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBMsg tcurl = Some msg ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
     ~(exists sid wt, st =wait (os_stat_mutexsem sid) wt).
Proof.
  introv Ht.
  pure_auto.
  apply H.
  simpl in Ht.
  mytac.
  inverts H4.
  funfold H7.
  destruct x4.
  destruct p.
  destruct p.
  mytac.
    apply tcbjoin_get_a in H6.
    rewrite H6 in *.
  destruct H9 as (_ & _ & _ & _ & _ & Hrts).
  funfold Hrts.
  funfold H13.
  inverts H2.
  specialize H13 with (prio := prio).
  specialize H13 with (eid := x).
  specialize H13 with (t_opt := x0).
  specialize H13 with (m := msg).
  pauto.
Qed.

Lemma low_stat_impl_high_stat_neq_mutex'
 : forall tcur tcurl tcblist2 rtbl tls1 tls2 tcbls st prio msg,
    TcbMod.join tls1 tls2 tcbls ->
     TCBList_P (Vptr tcur) (tcurl :: tcblist2) rtbl tls2 ->
     V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_MUTEX)) ->
     V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     V_OSTCBMsg tcurl = Some msg ->
     TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
     ~(exists sid wt, st =wait (os_stat_mutexsem sid) wt).
Proof.
  intros.
  lets Hget: TCBListP_head_in_tcb' H0 H2 H3.
  destruct Hget as [st' [sus]].
  lets Heq: TcbMod.join_get_r H H5.
  rewrite H4 in Heq; inverts Heq.
  lets Hget : low_stat_impl_high_stat_neq_mutex H0 H1 H2 H3 H5.
  pure_auto.
Qed.

Lemma RLH_ECB_ETbl_P_hold_for_update_mux_to_st
: forall tcbls ct p qid wt msg osevent etbl ey egrp' st petbl sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_mutexsem qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))), petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5];
unfold V_OSEventType in *;
intros;
assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto);
destruct Hpr1 as (Hpr1 & Hpr2);
lets Hvp: int_usign_eq Hpr1 Hpr2;
rewrite <- Hvp in H;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= $ prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi in H;
clear H1 Hpi;
rewrite Hvp in H;
destruct H;
assert (nq1: 0%nat <> 1%nat) by pauto;
lets Heq1: nth_upd_neq nq1 H0;
[ lets Hst: Hra1 H Heq1| lets Hst: Hra2 H Heq1 | lets Hst: Hra3 H Heq1 | lets Hst: Hra4 H Heq1 | lets Hst: Hra5 H Heq1];
destruct Hst as [tid]; do 3 destruct H2;
unfold get in *; unfold TcbMap in *;
exists tid x x0;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H3;
try (subst;
rewrite Htg in H2;
inverts H2);
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_mux_to_rdy
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_mutexsem qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl, petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))), petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
unfolds;
splits;
unfolds;
[ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4 | funfold Hrb5];
unfold V_OSEventType in *;
destruct Hrpt as (_ & _ & Hrpt);
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
[ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H | try eapply Hrb5 in H];
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

(* copy form sempend_pure_ext.v *)
Lemma Event_Type_P_hold_for_update
: forall osevent v n,
    n <> 0%nat ->
    Event_Type_P osevent ->
    Event_Type_P (update_nth_val n osevent (Vint32 v)).
Proof.
unfold Event_Type_P.
unfold V_OSEventType.
intros.
destruct H0 as [H1 | [H1 | [H1 | [H1 | H1]]]];
[left | right; left | do 2 right; left | do 3 right; left | do 4 right];
eapply nth_upd_neqrev; try pauto.
Qed.

Lemma EcbMod_get_join_sig_set:
forall  qls qid a qls1 b,
  EcbMod.join (EcbMod.sig qid b) qls1 qls ->
  EcbMod.get qls1 qid = None ->
  EcbMod.join (EcbMod.sig qid a) qls1 (EcbMod.set qls qid a).
Proof.
  intros.
  unfold EcbMod.join.
  intros.
  rewrite EcbMod.sig_sem.
  rewrite EcbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.beq_refl.
  rewrite H0. auto.
  eapply tidspec.neq_beq_false in H1.
  rewrite H1.
  destruct (EcbMod.get qls1 a0) eqn: eq2.
  lets Htg: EcbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (EcbMod.get qls a0 = EcbMod.get qls1 a0).
  eapply EcbMod.map_join_get_none; try eauto.
  rewrite EcbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.
(* end of copy *)

Lemma R_ECB_ETbl_P_hold_for_update_mux_to_rdy
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_mutexsem qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl, petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)), petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_mux_to_st; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_mux_to_rdy; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma RLH_ECBData_P_hold_mux
: forall pip o ct w ecbcurl,
  RLH_ECBData_P ecbcurl (absmutexsem pip o, w) ->
RLH_ECBData_P ecbcurl (absmutexsem pip o, remove_tid ct w).
Proof.
intros.
unfolds.
unfolds in H.
destruct ecbcurl; try tryfalse.
split; pauto.
simpl in *.
mytac.
split; intros.
apply H0 in H4.
subst.
simpl. auto.
splits;auto.
intros.
eapply H2.
pure_auto.
subst.
simpl in *.
tryfalse.
Qed.

Lemma ECBList_P_high_tcb_block_hold_mux_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_mutexsem qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  destruct p. (* new add *)
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits;
  unfolds;
  intros;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  mytac;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
  (* new add about petbl *)
  eapply R_ECB_PETbl_P_hold_for_set_rdy; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

(* new add *)
Lemma R_ECB_PETbl_P_high_tcb_block_hold':
  forall  l vl etbl petbl vl' etbl' petbl' tcbls prio st ptcb m' sus',
  ~( V_OSEventType vl = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) ->
  ~( V_OSEventType vl' = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) ->
  R_ECB_PETbl_P l (vl, etbl, petbl) tcbls ->
  ~(exists qid time, st = wait (os_stat_postq qid) time) ->
  R_ECB_PETbl_P l (vl', etbl', petbl') (TcbMod.set tcbls ptcb (prio, st, m', sus')).
Proof.
introv Hneq. intros.
funfold H0.
unfolds; splits; unfolds; intros.
rewrite H4 in H; tryfalse.
unfold get in *; unfold TcbMap in *.
assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto.
destruct Hc.
subst.
rewrite TcbMod.map_get_set in H3.
inverts H3.
false. eapply H1; eauto.
rewrite TcbMod.map_get_set' in H3; auto.
eapply H2 in H3.
destruct H3 as (H3 & Hf).
rewrite Hf in Hneq; tryfalse.
Qed.

Lemma ECBList_P_hold_for_update_mux_to_rdy
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold pip o wls petbl sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_mutexsem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmutexsem pip o, wls) ->
  In ct wls ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl, petbl) :: nil))  = Some (osevent,etbl, petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl, petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
  osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
  etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_MUTEX)) -> (* new add *)
  ECBList_P head Vnull (els1 ++ ((osevent',etbl', petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (absmutexsem pip o, remove_tid ct wls))
                        (TcbMod.set tcbls ct (p, rdy, msg, sus'))
.
Proof.
introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
introv Hgptr2 Hep Hey Het' Hetbl' Htp.
assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
destruct Hels1.
subst els1.
assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ecblist1.
simpl in *.
mytac.
destruct (beq_addrval qid x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
apply beq_addrval_eq in eq1.
subst x.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_mux_to_rdy; try eauto.
(* new add about petbl *)
eapply R_ECB_PETbl_P_high_tcb_block_hold'; eauto.
rewrite Htp; introv Hf; tryfalse.
eapply nth_upd_neqrev with (m:= 1%nat) in Htp.
rewrite Htp.
introv Hf; tryfalse.
auto with zarith.
introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf.
(* end of new add *)
exists (absmutexsem pip o, remove_tid ct wls) x1 x2.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply sempend_pure.ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H3. (* H2 -> H3 *)
destruct x0.
rewrite Heg in Heg'.
inverts Heg'.
eapply RLH_ECBData_P_hold_mux; auto.
eapply ECBList_P_high_tcb_block_hold_mux_to_rdy; try eauto.
eapply sempend_pure.ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
(* els1 <> nil *)
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
eapply ecblist_p_compose; try eauto.
Focus 2.
eapply ECBList_P_high_tcb_block_hold_mux_to_rdy; try eauto.
eapply sempend_pure.ejoin_get_none_l; [idtac | eauto].
eapply EcbMod.join_sig_get; eauto.
eapply EcbMod.my_joinsig_join_set; try eauto.
simpl.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_mux_to_rdy; try eauto.
(* new add about petbl *)
eapply R_ECB_PETbl_P_high_tcb_block_hold'; eauto.
rewrite Htp; introv Hf; tryfalse.
eapply nth_upd_neqrev with (m:= 1%nat) in Htp.
rewrite Htp.
introv Hf; tryfalse.
auto with zarith.
introv Hf. destruct Hf as (qd & qwt & Hf). inverts Hf.
(* end of new add *)
exists (absmutexsem pip o, remove_tid ct wls) x4 x5.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply sempend_pure.ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H7. (* H6 -> H7 *)
destruct x3.
lets Heg2: EcbMod.join_get_r H2 Heg'.
rewrite Heg in Heg2.
inverts Heg2.
eapply RLH_ECBData_P_hold_mux; auto.
eapply ECBList_P_high_tcb_block_hold_mux_to_rdy; try eauto.
eapply sempend_pure.ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_mux_to_rdy
: forall tcbls ct p qid wt msg ecbls pip o wls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_mutexsem qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmutexsem pip o, wls) ->
  In ct wls ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmutexsem pip o, remove_tid ct wls)) 
                                                    (TcbMod.set tcbls ct (p, rdy, msg, sus')) ct.
Proof.
introv Htg Heg Hi Hrte.
destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
unfolds;
splits;
unfolds;
[ funfold Hr1 | funfold Hr2 | funfold Hr3 | funfold Hr4 | funfold Hr5];
try splits;
intros.
{
assert (He: eid = qid \/ eid <> qid) by tauto;
rewrite EcbMod.set_sem in H3;
destruct He;
try (subst;
rewrite EcbMod.beq_refl in H3;
destruct H3;
inverts H3);
try(rewrite tidspec.neq_beq_false in H3; try auto;
eapply H in H3;
do 4 destruct H3;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H3;
inverts H3);
rewrite tidspec.neq_beq_false; try eauto).
}
{
(* new add about postq *)
assert ( eid = qid \/ eid <> qid) by tauto.
 rewrite EcbMod.set_sem in H3.
destruct H4.
subst;
rewrite EcbMod.beq_refl in H3;
destruct H3;
inverts H3.
rewrite tidspec.neq_beq_false in H3; try auto.
eapply H0 in H3.
do 4 destruct H3;
rewrite TcbMod.set_sem.
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H3;
inverts H3);
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in H3.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H4.
subst.
rewrite TcbMod.beq_refl in H3; inverts H3.
rewrite tidspec.neq_beq_false in H3; try eauto.
eapply H1 in H3.
mytac.
assert (Heq: eid = qid \/ eid <> qid) by tauto.
destruct Heq.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H3; inverts H3.
rewrite EcbMod.set_sem.
rewrite tidspec.neq_beq_false; try eauto.
repeat eexists; eauto.
}
{
rewrite TcbMod.set_sem in H3.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H4.
subst.
rewrite TcbMod.beq_refl in H3; inverts H3.
rewrite tidspec.neq_beq_false in H3; try eauto.
eapply H2 in H3.
mytac.
assert (Heq: eid = qid \/ eid <> qid) by tauto.
destruct Heq.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H3; inverts H3.
rewrite EcbMod.set_sem.
rewrite tidspec.neq_beq_false; try eauto.
repeat eexists; eauto.
}
{
assert (He: eid = qid \/ eid <> qid) by tauto;
rewrite EcbMod.set_sem in H1;
destruct He;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
rewrite tidspec.neq_beq_false in H1; try auto;
eapply H in H1;
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in H1.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H2.
subst.
rewrite TcbMod.beq_refl in H1; inverts H1.
rewrite tidspec.neq_beq_false in H1; try eauto.
eapply H0 in H1.
mytac.
assert (Heq: eid = qid \/ eid <> qid) by tauto.
destruct Heq.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H1; inverts H1.
rewrite EcbMod.set_sem.
rewrite tidspec.neq_beq_false; try eauto.
}
{
assert (He: eid = qid \/ eid <> qid) by tauto;
rewrite EcbMod.set_sem in H1;
destruct He;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
rewrite tidspec.neq_beq_false in H1; try auto;
eapply H in H1;
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in H1.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H2.
subst.
rewrite TcbMod.beq_refl in H1; inverts H1.
rewrite tidspec.neq_beq_false in H1; try eauto.
eapply H0 in H1.
mytac.
assert (Heq: eid = qid \/ eid <> qid) by tauto.
destruct Heq.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H1; inverts H1.
rewrite EcbMod.set_sem.
rewrite tidspec.neq_beq_false; try eauto.
}
{
  assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H3;
destruct H4.
subst;
rewrite EcbMod.beq_refl in H3.
destruct H3.
inverts H3.
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht.
subst;
unfold get in *; unfold TcbMap,EcbMap in *.
eapply in_remove_tid_false in H4;tryfalse.
rewrite tidspec.neq_beq_false; try eauto.
eapply in_remove_tid in H4.
eapply H;eauto.
rewrite tidspec.neq_beq_false in H3; try auto;
eapply H in H3;
do 4 destruct H3;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H3;
inverts H3);
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H4;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H3; try auto.
eapply H0 in H3;
do 4 destruct H3.
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H6.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H3.
inverts H3.
rewrite tidspec.eq_beq_true; auto.
repeat eexists; eauto.
eapply in_remove_tid'; eauto.
rewrite tidspec.neq_beq_false; try eauto.
}
eapply rh_tcblist_ecblist_mutex_owner_set'; eauto.
apply sem_common.Mutex_owner_hold_for_set_tcb; auto.
(* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
eapply OSTimeDlyPure.RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb
;eauto.
eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb'; eauto.
(* new add *)
{
assert (He: eid = qid \/ eid <> qid) by tauto;
rewrite EcbMod.set_sem in H1;
destruct He;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
rewrite tidspec.neq_beq_false in H1; try auto;
eapply H in H1;
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto.
}
{
rewrite TcbMod.set_sem in H1.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H2.
subst.
rewrite TcbMod.beq_refl in H1; inverts H1.
rewrite tidspec.neq_beq_false in H1; try eauto.
eapply H0 in H1.
mytac.
assert (Heq: eid = qid \/ eid <> qid) by tauto.
destruct Heq.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H1; inverts H1.
rewrite EcbMod.set_sem.
rewrite tidspec.neq_beq_false; try eauto.
}
Qed.


Lemma get_last_tcb_ptr_split:
forall vl1 vl2 x y,
 vl2 <> nil ->
 get_last_tcb_ptr vl2 x = Some y ->
 get_last_tcb_ptr (vl1 ++ vl2) x = Some y.
Proof.
induction vl1; intros.
simpl; auto.
lets Heq: IHvl1 H H0.
change ((a :: vl1) ++ vl2) with (a :: (vl1 ++ vl2)).
rewrite <- Heq.
unfold get_last_tcb_ptr.
simpl last.
destruct (vl1 ++ vl2) eqn: eq1.
eapply app_eq_nil in eq1.
simpljoin.
tryfalse.
auto.
Qed.

