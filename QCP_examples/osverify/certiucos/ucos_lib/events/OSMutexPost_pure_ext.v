Require Import include_frm.
Require Import math_auto.
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSTimeDlyPure.
Require Import Lia.

Require Import protect.
Require Import OSQPostPure.
Require Import OSMutex_common.
Require Import OSMutexPostPure.
Require Import ucos_include.
Require Import OSMutex_common.
Require Import OSTimeTickPure.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import sem_lab.
Require Import OSQPostPure.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

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

(* end of copy *)

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

(* copy from gjb_sem_common_ext_v1.v *)
Lemma Int8u_not_array_struct:
~ array_struct Int8u.
Proof.
unfold array_struct.
repeat ( try eapply Classical_Prop.and_not_or; split); 
repeat (try eapply Classical_Pred_Type.all_not_not_ex ; intros);
pure_auto.
Qed.
(* end copy *)

Lemma os_tcb_ptr_not_array_struct:
~ array_struct STRUCT os_tcb ⋆.
Proof.
unfold array_struct.
repeat ( try eapply Classical_Prop.and_not_or; split); 
repeat (try eapply Classical_Pred_Type.all_not_not_ex ; intros);
pure_auto.
Qed.

Lemma CurTCB_neq_vhold:
forall tcbls ct p1 p2 tcbl1 tcbcur tcbl2 rtbl ptbl ptls vhold s P,
s |= AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
        AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** P ->
ct <> vhold.
Proof.
unfold AOSTCBList.
unfold AOSTCBPrioTbl.
unfold tcbdllseg.
simpl dllseg.
unfold node.
intros.
sep normal in H.
do 7 destruct H.
sep split in H.
destruct H0.
destruct H4.
subst p2.
inverts H13.
eapply struct_type_vallist_match_os_tcb_flag in H12.
destruct H12. do 10 destruct H0.
subst tcbcur.
simpl Astruct in H.
assert (Hc: (x4, Int.zero) <> vhold \/ (x4, Int.zero) = vhold) by tauto.
destruct Hc. auto.
subst.
sep normal in H.
eapply pv_false in H.
tryfalse.
eapply Int8u_not_array_struct.
eapply os_tcb_ptr_not_array_struct.
Qed.

  Lemma disj_com_star :
  forall P Q R,  
    (P ** R) \\// (Q ** R) ==> (P \\// Q) ** R. 
Proof.
  intros.
  simpl in *.
  simpljoin.
  destruct H;
  mytac.
  do 6 eexists;splits; try left ; eauto.
  do 6 eexists;splits; try right ; eauto.
Qed.

  Lemma disj_com_star_gen :
  forall P Q R R',  
    R <==> R' ->
    (P ** R) \\// (Q ** R') ==> (P \\// Q) ** R. 
Proof.
  intros.
  simpl in *.
  simpljoin.
  destruct H0;
  mytac.
  join auto.
  join auto.
  destruct H with (substmo s x0 x3).
  eapply H6 in H5.
  unfold merge_list.
  rewrite jl_merge_emp.
  lets Heq: OSAbstMod.join_meq_eql OSAbstMod.map_join_emp.
  erewrite <- Heq. auto.
Qed.

Lemma return_r_pt_p' :
  forall v'52 x t m x10 v'45 v'43 v'39 v'30 v'51 sus sus',
    array_type_vallist_match OS_TCB ∗ v'30 ->
    length v'30 = 64%nat ->
    Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
    Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
    TcbJoin (v'52, Int.zero) ((x>>ᵢ$ 8), t, m, sus) x10 v'45 ->
    TcbMod.join v'43 v'45 v'39 ->
    Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true ->
    nth_val((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))))   v'30 = Some (Vptr (* v'51 *) (v'52, Int.zero) ) ->
    R_PrioTbl_P v'30 v'39 v'51 ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                      (update_nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                                      v'30 (Vptr (v'52, Int.zero))) (Vptr v'51))
      (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m, sus'))
      v'51.
Proof.
  introv Har Hlen Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hjo1.
  introv Hjo2 Hnneq Hntss  Hrp.
  unfolds.
  splits.
  introv Hp Hnth Hneq.
  unfolds in Hrp.
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  remember ( ∘(Int.unsigned prio)) as pm.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (pm <> pn \/ pm = pn) as Hart by tauto.
  destruct Hart as [Hart1 | Hart2].
  lets Hres : nth_upd_neq  Hart1 Hnth.
  assert (pm <> px \/ pm = px) as Harst by tauto.
  destruct Harst as [Harst1 | Harst2].
  lets Hres2 : nth_upd_neq  Harst1 Hres.
  lets Hasb : Hrp1 Hneq; eauto.
  rewrite <- Heqpm; auto. 
  unfolds in Hrp3.
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.

  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  unfold get in *; simpl in *.
  rewrite Hgs in Hsa.
  inverts Hsa.
  rewrite Heqpn in Hart1.
  rewrite Heqpm in Hart1.
  clear - Hart1.
  unfold nat_of_Z in Hart1.
  tryfalse.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  exists sst m11.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite Harst2 in Hres.
  lets Heqs: nth_upd_eq  Hres.
  inverts Heqs.
  exists t m.
  rewrite Heqpm in Harst2 .
  rewrite Heqpx in Harst2.
  assert (prio =x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 ).
  clear - Harst2 Hi6 Hp.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as xx.
  clear Heqxx.
  unfold nat_of_Z in Harst2.
  lets Has : Z2Nat.inj Harst2.  
  clear.
  int auto.
  clear .
  int auto.
  eapply unsigned_inj; eauto.
  rewrite H.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  rewrite Hart2 in Hnth.
  lets Heqs: nth_upd_eq  Hnth.
  inverts Heqs.
  tryfalse.

  introv Hgets .
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  unfold nat_of_Z.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (px = pn \/ px <> pn) as Hasrt by tauto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hasc : Hrp2 Hsa.
  destruct Hasc.
  split; auto.
  destruct Hasrt.
  apply Int.ltu_inv in Hnneq.
  rewrite Heqpn in H1.
  rewrite Heqpx in H1.
  clear -Hnneq H1.
  lets Heqx :  Z2Nat.inj H1;
    try
      eapply Int.unsigned_range; eauto.
  lia.
  eapply nth_upd_neqrev; eauto.
  assert (px < length v'30)%nat.
  clear - Hlen Heqpx Hi6.
  rewrite Hlen.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as Hk.
  rewrite Heqpx.
  clear Heqpx  HeqHk Hlen.
  mauto.
  lets Hass : ls_has_nth_val  H2.
  destruct Hass.
  eapply update_nth.
  eauto.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.neq_beq_false in Hgets; eauto.
  lets Hress : Hrp2 Hgets.
  destruct Hress.
  split; auto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hesx : Hrp3 H Hgets Hsa.

  
  eapply nth_upd_neqrev; eauto.
  unfold nat_of_Z.
  eapply  neq_imp_neqq ; eauto.
  remember  ∘(Int.unsigned prio) as px.
  remember  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) as py.

  assert (px <> py \/ px = py) as Hasss by tauto.
  destruct Hasss.
  eapply nth_upd_neqrev; eauto.
  rewrite H2 in *.
  rewrite H0 in Hntss.
  inverts Hntss.
  tryfalse.

  unfolds.
  intros.
  unfolds in Hrp.
  destruct Hrp as (Hpr1 & Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert ( (v'52, Int.zero) <> tid \/  (v'52, Int.zero) = tid ) by tauto.
  destruct H2.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.
  assert ( (v'52, Int.zero) <> tid' \/  (v'52, Int.zero) = tid' ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert (  prio <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H1; auto.
  subst prio.
  lets Hasds : Hpr2 H0.
  destruct Hasds.
  unfold nat_of_Z in H1.
  rewrite Hntss in H1.
  inverts H1.
  tryfalse.
  subst tid.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.
  assert (  prio' <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio' = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H0; auto.
  lets Hasds : Hpr2 H1.
  destruct Hasds.
  unfold nat_of_Z in H2.
  subst prio'.
  rewrite Hntss in H2.
  inverts H2.
  tryfalse.
Qed.

Lemma return_r_pt_p'' :
  forall v'52 x t m x10 v'45 v'43 v'39 v'30 v'51 sus sus',
    array_type_vallist_match OS_TCB ∗ v'30 ->
    length v'30 = 64%nat ->
    Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
    Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
    Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
    Int.unsigned (x>>ᵢ$ 8) < 64 ->
    Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
    TcbJoin (v'52, Int.zero) ((x>>ᵢ$ 8), t, m, sus) x10 v'45 ->
    TcbMod.join v'43 v'45 v'39 ->
    Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true ->
    nth_val((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))))   v'30 = Some ((* v'51 *) Vnull ) ->
    R_PrioTbl_P v'30 v'39 v'51 ->
    R_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))
                      (update_nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
                                      v'30 (Vptr (v'52, Int.zero))) (Vptr v'51))
      (TcbMod.set v'39 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, t, m, sus'))
      v'51.
Proof.
  introv Har Hlen Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hjo1.
  introv Hjo2 Hnneq Hntss  Hrp.
  unfolds.
  splits.
  introv Hp Hnth Hneq.
  unfolds in Hrp.
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  remember ( ∘(Int.unsigned prio)) as pm.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (pm <> pn \/ pm = pn) as Hart by tauto.
  destruct Hart as [Hart1 | Hart2].
  lets Hres : nth_upd_neq  Hart1 Hnth.
  assert (pm <> px \/ pm = px) as Harst by tauto.
  destruct Harst as [Harst1 | Harst2].
  lets Hres2 : nth_upd_neq  Harst1 Hres.
  lets Hasb : Hrp1 Hneq; eauto.
  rewrite <- Heqpm; auto. 
  unfolds in Hrp3.
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.

  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  unfold get in *; simpl in *.
  rewrite Hgs in Hsa.
  inverts Hsa.
  rewrite Heqpn in Hart1.
  rewrite Heqpm in Hart1.
  clear - Hart1.
  unfold nat_of_Z in Hart1.
  tryfalse.
  destruct Hasb as (sst & m11 & sus0 & Hgs).
  exists sst m11.
  rewrite TcbMod.set_sem.
  erewrite tidspec.neq_beq_false; eauto.
  rewrite Harst2 in Hres.
  lets Heqs: nth_upd_eq  Hres.
  inverts Heqs.
  exists t m.
  rewrite Heqpm in Harst2 .
  rewrite Heqpx in Harst2.
  assert (prio =x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 ).
  clear - Harst2 Hi6 Hp.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as xx.
  clear Heqxx.
  unfold nat_of_Z in Harst2.
  lets Has : Z2Nat.inj Harst2.  
  clear.
  int auto.
  clear .
  int auto.
  eapply unsigned_inj; eauto.
  rewrite H.
  rewrite TcbMod.set_sem.
  erewrite tidspec.eq_beq_true; eauto.
  rewrite Hart2 in Hnth.
  lets Heqs: nth_upd_eq  Hnth.
  inverts Heqs.
  tryfalse.

  introv Hgets .
  destruct Hrp as (Hrp1 & Hrp2 & Hrp3).
  assert ( tcbid =  (v'52, Int.zero) \/ tcbid <>  (v'52, Int.zero)) by tauto.
  destruct H.
  subst tcbid.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.eq_beq_true in Hgets; eauto.
  inverts Hgets.
  unfold nat_of_Z.
  remember ( (Z.to_nat (Int.unsigned (x>>ᵢ$ 8)))) as pn.
  remember ((Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))) as px.
  assert (px = pn \/ px <> pn) as Hasrt by tauto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hasc : Hrp2 Hsa.
  destruct Hasc.
  split; auto.
  destruct Hasrt.
  apply Int.ltu_inv in Hnneq.
  rewrite Heqpn in H1.
  rewrite Heqpx in H1.
  clear -Hnneq H1.
  lets Heqx :  Z2Nat.inj H1;
    try
      eapply Int.unsigned_range; eauto.
  lia.
  eapply nth_upd_neqrev; eauto.
  assert (px < length v'30)%nat.
  clear - Hlen Heqpx Hi6.
  rewrite Hlen.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as Hk.
  rewrite Heqpx.
  clear Heqpx  HeqHk Hlen.
  mauto.
  lets Hass : ls_has_nth_val  H2.
  destruct Hass.
  eapply update_nth.
  eauto.
  rewrite TcbMod.set_sem in Hgets.
  erewrite tidspec.neq_beq_false in Hgets; eauto.
  lets Hress : Hrp2 Hgets.
  destruct Hress.
  split; auto.
  lets Hsa : tcbjoin_mod Hjo1 Hjo2.
  lets Hesx : Hrp3 H Hgets Hsa.

  
  eapply nth_upd_neqrev; eauto.
  unfold nat_of_Z.
  eapply  neq_imp_neqq ; eauto.
  remember  ∘(Int.unsigned prio) as px.
  remember  (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) as py.

  assert (px <> py \/ px = py) as Hasss by tauto.
  destruct Hasss.
  eapply nth_upd_neqrev; eauto.
  rewrite H2 in *.
  rewrite H0 in Hntss.
  inverts Hntss.
(*   tryfalse. *)

  unfolds.
  intros.
  unfolds in Hrp.
  destruct Hrp as (Hpr1 & Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert ( (v'52, Int.zero) <> tid \/  (v'52, Int.zero) = tid ) by tauto.
  destruct H2.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.neq_beq_false in H0; eauto.
  assert ( (v'52, Int.zero) <> tid' \/  (v'52, Int.zero) = tid' ) by tauto.
  destruct H3.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1; eauto.
  inverts H1.
  assert (  prio <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H1; auto.
  subst prio.
  lets Hasds : Hpr2 H0.
  destruct Hasds.
  unfold nat_of_Z in H1.
  rewrite Hntss in H1.
  inverts H1.
  tryfalse.
  subst tid.
  rewrite TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; eauto.
  rewrite TcbMod.set_sem in H0.
  rewrite tidspec.eq_beq_true in H0; eauto.
  inverts H0.
  assert (  prio' <> x&ᵢ$ OS_MUTEX_KEEP_LOWER_8 \/   prio' = x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) by tauto.
  destruct H0; auto.
  lets Hasds : Hpr2 H1.
  destruct Hasds.
  unfold nat_of_Z in H2.
  subst prio'.
  rewrite Hntss in H2.
  inverts H2.
(*   tryfalse. *)
Qed.

Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold':
  forall (prio : Z) (y bitx : int32) (rtbl : vallist) 
         (ry : int32) (ptbl : vallist) (av : addrval),
    0 <= prio < 64 ->
    y = $ prio>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ($ prio&ᵢ$ 7) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl av ->
    RL_RTbl_PrioTbl_P
      (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx)))
      (update_nth_val  (∘prio)  ptbl (Vptr av))
      av.
Proof.
  introv Hpr Hy Hb Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  introv Hp Hpro.
  subst .
  remember ($ prio) as pri.
  assert ( 0 <= Int.unsigned pri < 64).
  clear -Hpr Heqpri.
  subst.
  int auto.
  assert (p = pri \/ p <> pri) by tauto.
  destruct H0.
  subst p.
  eapply  prio_update_self_not_in in Hpro; eauto.
  tryfalse.
  lets Hxs : prio_neq_in_tbl H0 Hnth Hpro; eauto.
  lets Has : Hrl Hxs; eauto.
  simpljoin.
  exists x.
  splits; auto.
  assert ((Z.to_nat (Int.unsigned p)) <> ∘prio).
  unfold nat_of_Z.
  introv Hf.
  apply H0.
  lets Hsas : Z2Nat.inj Hf; eauto.
  rewrite <- Hsas.
  clear - H5.
  int auto.
  eapply nth_upd_neqrev; eauto.
Qed.

Lemma mutex_nowt_imp_tcb_st :
  forall els tls ct eid pip prio p st m sus,
    RH_TCBList_ECBList_P els tls ct ->
    EcbMod.get els eid = Some (absmutexsem pip (Some (ct, prio)), nil) ->
    TcbMod.get tls ct = Some (p,st,m, sus) ->
    ~(exists t, st = wait (os_stat_mutexsem eid) t)
.
Proof.
introv Hrte Hget_e Hget_t.
funfold Hrte.
assert (Hst: (exists t, st = wait (os_stat_mutexsem eid) t) 
                      \/ ~(exists t, st = wait (os_stat_mutexsem eid) t)) by tauto.
destruct Hst as [(t & Hst) | Hst].
subst.
funfold H2.
eapply H4 in Hget_t.
destruct Hget_t as (n1 & n2 & wl & Hget & Hin).
unfold get in Hget. unfold EcbMap in Hget.
rewrite Hget_e in Hget.
inverts Hget.
apply in_nil in Hin.
tryfalse.
auto.
Qed.

Lemma return_r_ecb_et_p' :
  forall els tls ct eid pip prio p st m p' i x x3 v'46 etbl petbl sus sus',
    RH_TCBList_ECBList_P els tls ct ->
    EcbMod.get els eid = Some (absmutexsem pip (Some (ct, prio)), nil) ->
    TcbMod.get tls ct = Some (p,st,m, sus) ->
    R_ECB_ETbl_P eid
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vptr ct :: x3 :: v'46 :: nil,
                  etbl, petbl) tls ->
    R_ECB_ETbl_P eid
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 i :: Vint32 x :: Vptr ct :: x3 :: v'46 :: nil, etbl, petbl)
                 (TcbMod.set tls ct (p', st, m, sus')).
Proof.
introv Hrte Hget_e Hget_t Hr.
lets Hst: mutex_nowt_imp_tcb_st Hrte Hget_e Hget_t.
funfold Hr.
unfolds.
splits.
 funfold H.
  unfolds.
  splits; unfolds; intros;
  try (unfold V_OSEventType in H6; simpl in H6; tryfalse).
  eapply H4 in H6. unfold V_OSEventType in H6; simpl in H6.
  eapply H6 in H7. do 4 destruct H7.
  rename x4 into sus0.
  exists x0.
  rewrite TcbMod.set_sem.
  destruct (tidspec.beq ct x0) eqn:eq1.
  eapply tidspec.beq_true_eq in eq1.
  subst.
  unfold get in *. unfold TcbMap,EcbMap in *.
  rewrite Hget_t in H7.
  inverts H7.
  false.
  eapply Hst. eauto.
  eauto.
  funfold H0.
  unfolds.
  splits; unfolds; intros;
  rewrite TcbMod.set_sem in H6;
  destruct (tidspec.beq ct tid) eqn:eq1;
  try eapply H0 in H6;
  try eapply H2 in H6;
  try eapply H3 in H6;
  try eapply H4 in H6;
  try eapply H5 in H6; auto;
  eapply tidspec.beq_true_eq in eq1;
  subst; inverts H6;
  try eapply H0 in Hget_t;
  try eapply H2 in Hget_t;
  try eapply H3 in Hget_t;
  try eapply H4 in Hget_t;
  try eapply H5 in Hget_t;
  destruct Hget_t as (Hp & Hv);
  unfold V_OSEventType in Hv; simpl in Hv; tryfalse.
  false. eapply Hst. eauto.
  unfolds. unfold V_OSEventType.
  simpl. auto. 
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
intros.
destruct (tidspec.beq pid eid) eqn: eq1.
eapply tidspec.beq_true_eq in eq1.
subst.
eapply H0 in H1; eauto.
do 3 destruct H1.
rewrite EcbMod.set_sem. rewrite TcbMod.beq_refl.
repeat eexists.
rewrite EcbMod.set_sem. rewrite eq1.
eapply H0 in H1. eauto. auto.
Qed.

Lemma vnull_not_get:
  forall tcbls_l tcbls_r tcbls ct cur_prio x2 v'32 v'53 phold sus,
    TcbMod.join tcbls_l tcbls_r tcbls ->
    TcbJoin ct (cur_prio, rdy, Vnull, sus) x2 tcbls_r -> 
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 =
    Vnull ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg) sus,
      TcbMod.get x2 tid = Some (p, s0, m, sus) -> p <> phold.
Proof.
  intros.
  unfolds in H1.
  destructs H1.
  unfolds in H5.
  assert (TcbMod.get tcbls tid = Some (p,s0,m, sus0)).
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get_my;eauto.
  clear H3.
  intro.
  subst p.
  lets Hx:H4 H6.
  destruct Hx.
  apply nth_val_nth_val'_some_eq in H3;auto.
  unfold nat_of_Z in H3.
  rewrite H3 in H2.
  inverts H2.
Qed.

Lemma vnull_not_get'
: forall (tcbls_l tcbls_r tcbls : TcbMod.map) 
         (v'32 : vallist) (v'53 : addrval) (phold : int32),
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls v'53 ->
    nth_val' (Z.to_nat (Int.unsigned phold)) v'32 = Vnull ->
    forall (tid : tidspec.A) (p : priority) (s0 : taskstatus) (m : msg) sus,
      TcbMod.get tcbls_l tid = Some (p, s0, m, sus) -> p <> phold.
Proof.
  intros.
  unfolds in H0.
  simpljoin.
  assert (TcbMod.get tcbls tid = Some (p,s0,m, sus)).
  eapply TcbMod.join_get_l;eauto.
  clear H2.
  intro.
  subst p.
  apply H3 in H5.
  destruct H5.
  unfold nat_of_Z in H2.
  apply nth_val_nth_val'_some_eq in H2;auto.
  rewrite H1 in H2;inverts H2.
Qed.
Lemma return_tcbl_p'' :
forall v'31 v'33 v'36 v'43 x x11 t1 x12 v'51 v'39 v'30 v'45 x10 t m v'52 v'22 sus,
                        array_type_vallist_match Int8u v'36 ->
                        length v'36 = ∘OS_RDY_TBL_SIZE ->
                        Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
                        Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
                        Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
                        Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
                        Int.unsigned (x>>ᵢ$ 8) < 64 ->
                        Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
                                 OSMapVallist = Vint32 x11 ->
                        true = rule_type_val_match Int8u (Vint32 x11) ->
                        Int.unsigned x12 <= 255 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
                        Vint32 x12 ->
                        nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                 (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                 (val_inj
                                                    (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
                        Vint32 t1 ->
                        Int.unsigned t1 <= 255 ->
                        TcbMod.join v'43 v'45 v'39 ->
                        TcbJoin (v'52, Int.zero) (x>>ᵢ$ 8, t, m, sus) x10 v'45 ->
                        (* (nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
                        Some (Vptr v'51)) -> *)
                        (get v'22 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some Null \/
                        get v'22 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some Holder) ->
                       RH_PrioTbl_P v'30 v'22 v'51 ->
                        R_PrioTbl_P v'30 v'39 v'51 ->
                        TCBList_P v'31 v'33 v'36 v'43 ->
                        TCBList_P v'31 v'33
                                  (update_nth_val
                                     (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                     (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                     (val_inj
                                                        (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                                     (val_inj (or (Vint32 t1) (Vint32 x11)))) v'43
.
Proof.
  intros.
  simpl val_inj in *.
  apply math_mapval_core_prop in H7;auto.
  subst x11.
  eapply OSQPostPure.TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  remember ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) as X;clear HeqX.
  clear;int auto.
  eapply OSQPostPure.nth_val'2nth_val;eauto.
  unfold RH_PrioTbl_P in H16.
  destruct H16 as (Hlh & Hhl).
  unfold RHL_PrioTbl_P in Hhl.
  destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & HhL4).
  destruct H15 as [Hnul | Hhold].
  eapply Hhl2 in Hnul; eauto. destruct Hnul as (Hr & Hn).
  intros.
  eapply vnull_not_get';eauto.
  eapply nth_val_nth_val'_some_eq;eauto. 
  eapply Hhl3 in Hhold; eauto. destruct Hhold as (Hr & Hn).
  intros.
  eapply vhold_not_get';eauto.
  eapply nth_val_nth_val'_some_eq;eauto. 
  eapply Mbox_common.TCBList_P_tcb_block_hold';eauto.
  split;auto.
  remember (x>>ᵢ$ 8) as X;clear HeqX.
  clear;int auto.
  eapply tcbjoin_get_a_my;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  split;auto.
  remember (x>>ᵢ$ 8) as X.
  clear;int auto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a_my;eauto.
  eapply OSQPostPure.nth_val'2nth_val;eauto.
Qed.

Lemma tcbls_l_mutexpend1:
  forall prio_lift  ptcb_prio v'33 v'34 v'45 v'43 x11 xm i8 ptcb_tcby ptcb_bitx ptcb_bity v'36
                os_rdy_tbl tcbls_l v'32 tcbls_r tcbls ptcb_addr v0 x5 vhold sus,
    
    get_last_tcb_ptr v'34 v'33 = Some (Vptr (ptcb_addr,Int.zero)) -> (*added*)
    nth_val' (Z.to_nat (Int.unsigned prio_lift)) v'32 =
    Vnull -> (*added*)
    TcbMod.join tcbls_l tcbls_r tcbls ->
    R_PrioTbl_P v'32 tcbls vhold ->
    Int.unsigned prio_lift < 64 -> 
    ptcb_prio <>  prio_lift->
    TcbMod.get tcbls_l (ptcb_addr, Int.zero) =
    Some (ptcb_prio, rdy, xm, sus) ->
    nth_val' (Z.to_nat (Int.unsigned ptcb_tcby)) os_rdy_tbl =
    Vint32 v0 ->
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
  introv Hlast Hhold.
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
  rewrite Hlast in H6;inverts H6.
  exists x6.
  eapply tcbjoin_get_a_my;eauto.
  eapply TCBList_P_rtbl_add_simpl_version;eauto.
  split;auto.
  clear;int auto.
  apply nth_val'2nth_val;auto.
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg) sus,
            TcbMod.get tcbls_l tid = Some (p, s, m, sus) -> p <> prio_lift).
  eapply vnull_not_get';eauto.
  intros.
  eapply H9;eauto.
  eapply TcbMod.join_get_l;eauto.
  destruct x6.
  destruct p as ((p&st)&m).
  Require Import Mbox_common.
  eapply TCBList_P_tcb_block_hold' with (tcs:= x1) (tcs':=tcbls_l) (prio:=p);eauto.
  clear -H12.
  unfolds in H12.

  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  clear -H12.
  unfolds in H12.
  simpljoin.
  unfolds in H1.
  simpljoin.
  simpl_vqm.
  auto.
  unfolds in H12.
  simpljoin.
  unfolds in H12.
  simpljoin.
  symmetry in H6.
  symmetry in Hlast.
  symmetry in H3.
  simpl_vqm.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply TcbMod_join_impl_prio_neq_cur_l;eauto.
  eapply R_PrioTbl_P_impl_prio_neq_cur;eauto.
  eapply TcbMod.join_get_l;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_a_my;eauto.
  clear -H12 H4.
  unfolds in H12.
  Import DeprecatedTactic.
  mytac.
  unfolds in H1.
  mytac.
  simpl_vqm.
  apply nth_val'2nth_val;auto.
  simpl.
  rewrite Hlast in H6;inverts H6.
  do 4 eexists;splits;eauto.
  unfolds;simpl;eauto.
  instantiate (1:= x4).
  instantiate (1:= (prio_lift, rdy, xm, sus)).
  eapply tcbjoin_set_my;eauto.
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
  mytac.
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
  eexists;split.
  unfolds;simpl;auto.
  intros.
  apply H26;auto.
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
  left. (*add*)
  split;eauto.

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
  assert (forall (tid : tidspec.A) (p : priority) (s : taskstatus) (m : msg) sus,
            TcbMod.get tcbls_l tid = Some (p, s, m, sus) -> p <> prio_lift).
  eapply vnull_not_get';eauto.
  intros.
  destruct x6.
  destruct p0.
  destruct p0.
  eapply H6;eauto.
  eapply TcbMod.join_get_r;eauto.
  eapply tcbjoin_get_get;eauto.
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
  eapply TCBList_P_tcb_block_hold' with (tcs:= TcbMod.sig (ptcb_addr, Int.zero) (p, t, m,s)) (tcs':=x1) (prio:=p);eauto.
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

Lemma return_tcbl_p_alt: 
forall  m x x11 x8 v'22 v'35 v'36 x12 t1  v'52 v'45 v'24 x15 x7 v'51 v'39 v'30 x10 v'43 sus,
                       nth_val'
                         (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                         OSMapVallist = Vint32 x8 ->
                       true = rule_type_val_match Int8u (Vint32 x8) ->
                       Int.ltu (x>>ᵢ$ 8) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true->
                       array_type_vallist_match Int8u v'36 ->
                       length v'36 = ∘OS_RDY_TBL_SIZE ->
                       Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3) < 8 ->
                       Int.unsigned ((x>>ᵢ$ 8)&ᵢ$ 7) < 8 ->
                       Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 ->
                       Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3) < 8 ->
                       Int.unsigned (x>>ᵢ$ 8) < 64 ->
                       Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) < 64 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)))
                                OSMapVallist = Vint32 x11 ->
                       true = rule_type_val_match Int8u (Vint32 x11) ->
                       Int.unsigned x12 <= 255 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36 =
                       Vint32 x12 ->
                       nth_val' (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                (val_inj
                                                   (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))))))) =
                       Vint32 t1 ->
                       Int.unsigned t1 <= 255 ->
                       TcbMod.join v'43 v'45 v'39 ->
                       TcbJoin (v'52, Int.zero) (x>>ᵢ$ 8, rdy, m, sus) x10 v'45 ->
                      (*  nth_val (Z.to_nat (Int.unsigned (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'30 =
                       Some (Vptr v'51) ->  *)
                       (get v'22 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some Null \/
                        get v'22 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some Holder) ->
                       RH_PrioTbl_P v'30 v'22 v'51 ->
                       R_PrioTbl_P v'30 v'39 v'51 ->
                       TCBList_P (Vptr (v'52, Int.zero))
                                 ((x7
                                     :: v'24
                                     :: x15
                                     :: m
                                     :: V$0
                                     :: V$OS_STAT_RDY
                                     :: Vint32 (x>>ᵢ$ 8)
                                     :: Vint32 ((x>>ᵢ$ 8)&ᵢ$ 7)
                                     :: Vint32 ((x>>ᵢ$ 8)>>ᵢ$ 3)
                                     :: Vint32 ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7))
                                     :: Vint32 ($ 1<<ᵢ((x>>ᵢ$ 8)>>ᵢ$ 3))
                                     :: nil) :: v'35) v'36 v'45 ->
                       TCBList_P (Vptr (v'52, Int.zero))
                                 ((x7
                                     :: v'24
                                     :: x15
                                     :: m
                                     :: V$0
                                     :: V$OS_STAT_RDY
                                     :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                     :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                     :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                                     :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35)
                                 (update_nth_val
                                    (Z.to_nat (Int.unsigned ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)))
                                    (update_nth_val (Z.to_nat (Int.unsigned ((x>>ᵢ$ 8)>>ᵢ$ 3))) v'36
                                                    (val_inj
                                                       (and (Vint32 x12) (Vint32 (Int.not ($ 1<<ᵢ((x>>ᵢ$ 8)&ᵢ$ 7)))))))
                                    (val_inj (or (Vint32 t1) (Vint32 x11))))
                                 (TcbMod.set v'45 (v'52, Int.zero) (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, m, sus)).
Proof.
  introv Hadd1 Hadd2.
  intros.
  simpl val_inj in *.
  assert (nil++ (x7
                   :: v'24
                   :: x15
                   :: m
                   :: V$0
                   :: V$OS_STAT_RDY
                   :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                   :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                   :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                   :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35 =(x7
                                                                  :: v'24
                                                                  :: x15
                                                                  :: m
                                                                  :: V$0
                                                                  :: V$OS_STAT_RDY
                                                                  :: Vint32 (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                                                  :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                                                  :: Vint32 ((x&ᵢ$ OS_MUTEX_KEEP_LOWER_8)>>ᵢ$ 3)
                                                                  :: Vint32 x11 :: Vint32 x8 :: nil) :: v'35).
  simpl;auto.
  rewrite <- H20.
  clear H20.
  eapply math_mapval_core_prop in H8;eauto.
  subst x11.
  eapply math_mapval_core_prop in Hadd1;eauto.
  subst x8.
  destruct H16 as [Hgnul | Hghol].
  unfold RH_PrioTbl_P in H17.
  destruct H17 as (Hlh & Hhl).
  destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & Hhl4).
  eapply Hhl2 in Hgnul. destruct Hgnul as (Hr & Hnul).
  eapply tcbls_l_mutexpend1; eauto. 
  eapply nth_val_nth_val'_some_eq; eauto. 
  eapply TcbMod.join_comm;eauto.
  clear -H.
  intro.
  rewrite H0 in H;clear -H.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  clear HeqX.
  int auto.
  eapply tcbjoin_get_a_my;eauto.
  unfold RH_PrioTbl_P in H17.
  destruct H17 as (Hlh & Hhl).
  destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & Hhl4).
  eapply Hhl3 in Hghol. destruct Hghol as (Hr & Hnul).
  eapply tcbls_l_mutexpend; eauto. 
  eapply nth_val_nth_val'_some_eq; eauto. 
  eapply TcbMod.join_comm;eauto.
  clear -H.
  intro.
  rewrite H0 in H;clear -H.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as X.
  clear HeqX.
  int auto.
  eapply tcbjoin_get_a_my;eauto.
Qed.

Lemma double_update_simpl
: forall vl n v1 v2,
  (n < length vl)%nat ->
  update_nth_val n (update_nth_val n vl v1) v2 = update_nth_val n vl v2.
Proof.
induction vl; intros.
simpl; auto.
simpl in *.
destruct n.
simpl. auto.
eapply lt_S_n in H.
eapply IHvl in H.
simpl.
erewrite H.
auto.
Qed.

Lemma prio_available_join_l
: forall pr tls1 tls2 tls,
join tls1 tls2 tls ->
prio_available pr tls ->
prio_available pr tls1.
Proof.
unfold prio_available.
intros.
eapply H0.
eapply TcbMod.join_get_l; eauto.
Qed.

Lemma prio_available_join_r
: forall pr tls1 tls2 tls,
join tls1 tls2 tls ->
prio_available pr tls ->
prio_available pr tls2.
Proof.
unfold prio_available.
intros.
eapply H0.
eapply TcbMod.join_get_r; eauto.
Qed.

Lemma R_PrioTbl_P_update_vhold'
: forall pr ptbl tls vhold, 
            R_PrioTbl_P ptbl tls vhold ->
            prio_available pr tls ->
            R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned pr)) ptbl (Vptr vhold)) tls vhold.
Proof.
  intros.
  funfold H.
  unfolds.
  splits; intros; auto.
  eapply H; auto.
  eapply nth_upd_neq ; [idtac | eauto].
  assert ((∘(Int.unsigned prio) = Z.to_nat (Int.unsigned pr))
                \/ ∘(Int.unsigned prio) <> (Z.to_nat (Int.unsigned pr))) by tauto.
  destruct H6; auto.
  rewrite H6 in H4.
  eapply nth_upd_eq in H4.
  inverts H4. tryfalse.
  lets Hneq: H0 H3.
  eapply H1 in H3.
  destruct H3.
  split; auto.
  eapply nth_upd_neqrev; eauto.
  unfold nat_of_Z.
  eapply semacc_int_eq_false in Hneq.
  eapply neq_imp_neqq; auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_update_vhold' 
: forall pr rtbl ptbl tls vhold, 
            R_PrioTbl_P ptbl tls vhold ->
            RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
            prio_available pr tls ->
            RL_RTbl_PrioTbl_P rtbl (update_nth_val (Z.to_nat (Int.unsigned pr)) ptbl (Vptr vhold)) vhold.
Proof.
  unfold RL_RTbl_PrioTbl_P in *.
  intros.
  lets aa : H0 H2 H3.
  destruct aa as (tid & Hn & Hneq).
  eexists; splits; eauto.
  assert ((∘(Int.unsigned p) = Z.to_nat (Int.unsigned pr))
                \/ ∘(Int.unsigned p) <> (Z.to_nat (Int.unsigned pr))) by tauto.
  destruct H4.
  funfold H.
  eapply H in Hn; eauto.
  destruct Hn as (st & m & sus & Hget).
  eapply H1 in Hget.
  eapply semacc_int_eq_false in Hget.
  unfold nat_of_Z in H4.
  eapply neq_imp_neqq in Hget.
  tryfalse.
  eapply nth_upd_neqrev; eauto.
Qed.

Lemma rh_tcblist_ecblist_p_post_exwt_mutex'
: forall (v'8 tid : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (xl : option int32) x t op st m pt sus sus' sus'',
    TcbMod.get v'7 t = Some (op,st,m,sus) ->
    op <> x ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmutexsem x (Some (t, pt)), x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio, wait (os_stat_mutexsem eid) xl, msg0, sus') ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid (absmutexsem x (Some (tid, prio)), remove_tid tid x1))
      (TcbMod.set v'7 tid (prio, rdy, Vnull, sus'')) v'8.
Proof.
  introv ml Ht Hneq.
  intros.
  destruct H as (Hq & Hsem & Hmbox & Hmut & Hport).
  destruct Hq as (Hq1 & Hpostq1 & Hq2& Hpostq2).
  destruct Hsem as (Hsem1 & Hsem2).
  destruct Hmbox as (Hmbox1 & Hmbox2).
  destruct Hmut as (Hmut1 & Hmut2 & Hown & Howp).
  destruct Hport as (Hport1 & Hport2).
  unfold get in *; unfold TcbMap, EcbMap in *.
  unfolds;splits.

  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hq1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 4 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2. destruct H; inverts H.
  eapply Hpostq1 in H.  
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 4 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1.  inverts H.
  eapply Hq2 in H. destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  do 5 destruct H. rewrite H in H1; inverts H1. do 4 destruct H;
  repeat eexists; destruct H; eauto.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1.  inverts H.
  eapply Hpostq2 in H. destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  do 5 destruct H. rewrite H in H1; inverts H1. do 4 destruct H;
  repeat eexists; destruct H; eauto.

  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hsem1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 4 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
   destruct (tidspec.beq tid tid0) eqn: eq1; inverts H.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  eapply Hsem2 in H5.
  destruct H5. do 2 destruct H. rewrite H in H1; inverts H1.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.

  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hmbox1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 4 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
   destruct (tidspec.beq tid tid0) eqn: eq1; inverts H.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  eapply Hmbox2 in H5.
  destruct H5. do 2 destruct H. rewrite H in H1; inverts H1.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
(*RH_TCBList_ECBList_MUTEX_P*)
  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply Hmut1 in H.
  (try destruct H; inverts H).
          mytac;
          destruct (tidspec.beq tid tid0) eqn: eq1; eauto;
          try (eapply tidspec.beq_true_eq in eq1;
          subst; rewrite H3 in H;
          inverts H).
   eapply tidspec.beq_true_eq in eq2. subst.
   eapply tidspec.beq_true_eq in eq1. subst.
   eapply in_remove_tid_false in H4; tryfalse.
   eapply tidspec.beq_true_eq in eq2. subst.
   eapply go.ecbmod_joinsig_get in H1.
  eapply EcbMod.join_get_r in H1; eauto.
  eapply Hmut1. split; eauto.
  eapply in_remove_tid; eauto.
  destruct (tidspec.beq tid tid0) eqn: eq1.
   eapply tidspec.beq_true_eq in eq1. subst.
  eapply Hmut1 in H.
  rewrite H3 in H.
  do 4 destruct H. inverts H. rewrite TcbMod.beq_refl in eq2. tryfalse.
  eapply Hmut1 in H. 
  lets He: go.ecbmod_joinsig_get H1.
  eapply EcbMod.join_get_r in He; eauto.

  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1;
  inverts H; tryfalse.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  eapply tidspec.beq_true_eq in eq2.
  subst.
  lets He: go.ecbmod_joinsig_get H1.
  eapply EcbMod.join_get_r in He; eauto.
  lets Hin: Hmut2 H5.
  destruct Hin as (en1 & en2 & ew & He' & Hin).
  rewrite He in He'. inverts He'.
  repeat eexists.
  eapply in_neq_remove_in; try eapply tidspec.beq_false_neq; eauto.
  eapply Hmut2; eauto.
  unfolds; intros.
  rewrite TcbMod.set_sem;
  destruct (tidspec.beq tid tid0) eqn: eq1; eauto;
   try eapply tidspec.beq_true_eq in eq1; subst;
  rewrite EcbMod.set_sem in H;
  destruct (tidspec.beq eid eid0) eqn: eq2;
  try eapply tidspec.beq_true_eq in eq2; subst.
  inverts H.
  split; try eapply in_wtset_rm_notin; eauto.
  lets Hin: Hown H.
  destruct Hin as (_ & Hin).
  splits; eauto.
  inverts H.
  rewrite TcbMod.beq_refl in eq1; tryfalse.
  eapply Hown; eauto.
  (*RH_TCBList_ECBList_MUTEX_OWNER_P *)
  lets He: EcbMod.join_joinsig_get H0 H1.
  lets Hot': Hown He.
  destruct Hot' as (_ & Hin).
Require Import OSTimeDlyPure.
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  unfolds; splits; intros.
  rewrite EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2. inverts H; tryfalse.
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp.
  destruct Howp as (Hno & Hpv & Hne).
  eapply Hno; eauto.
  rewrite EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2;  inverts H;
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp;
  destruct Howp as (Hno & Hpv & Hne);
  eapply Hpv; eauto.  
  rewrite EcbMod.set_sem in *.
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp;
  destruct Howp as (Hno & Hpv & Hne).
  destruct (tidspec.beq eid eid1) eqn: eq1;  destruct (tidspec.beq eid eid2) eqn: eq2.
  eapply tidspec.beq_true_eq in eq1, eq2. subst. tryfalse.
  eapply tidspec.beq_true_eq in eq1. subst. inverts H.
  eapply go.ecbmod_joinsig_get in H1. eapply Hne; eauto.
  eapply tidspec.beq_true_eq in eq2. subst. inverts H4.
  eapply go.ecbmod_joinsig_get in H1; eauto.
  eapply Hne; eauto.

  (* new add *)
  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hport1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 4 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
   destruct (tidspec.beq tid tid0) eqn: eq1; inverts H.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  eapply Hport2 in H5.
  destruct H5. destruct H. rewrite H in H1; inverts H1.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
Qed.

Lemma R_Prio_No_Dup_hold_gen
: forall p p' tls st st' m m' sus sus' tid,
  prio_available p' tls ->
  TcbMod.get tls tid = Some (p, st, m, sus) ->
  R_Prio_No_Dup tls ->
  R_Prio_No_Dup (TcbMod.set tls tid (p', st', m', sus')).
Proof.
unfold R_Prio_No_Dup.
intros.
rewrite TcbMod.set_sem in *.
destruct (tidspec.beq tid tid0) eqn: eq1.
apply tidspec.beq_true_eq in eq1.
subst.
destruct (tidspec.beq tid0 tid') eqn: eq2;
try (apply tidspec.beq_true_eq in eq2; subst ; tryfalse).
inverts H3.
eapply semacc_int_eq_false.
eapply H; eauto.
destruct (tidspec.beq tid tid') eqn: eq2.
apply tidspec.beq_true_eq in eq2; subst.
inverts H4.
eapply semacc_int_eq_false.
rewrite Int.eq_sym.
eapply H; eauto.
eapply H1; eauto.
Qed.

Lemma R_Prio_No_Dup_hold_ptls_gen'
: forall p p' tls st st' m m' sus sus' tid ptbl ptls,
(get ptls p' = Some Null \/
  get ptls p' = Some Holder)->
  R_PrioTbl_P ptbl tls vhold_addr ->
  RH_PrioTbl_P ptbl ptls vhold_addr ->
  TcbMod.get tls tid = Some (p, st, m, sus) ->
  R_Prio_No_Dup tls ->
  R_Prio_No_Dup (TcbMod.set tls tid (p', st', m', sus')).
Proof.
      intros.
      unfolds in H0. unfolds in H1.
      simpljoin.
      unfolds.
      intros.
      assert ( tid = tid0 \/ tid <> tid0) by tauto.
      destruct H10; intros.
      subst tid.
      unfold get in *; simpl in *.
      rewrite TcbMod.set_a_get_a in H8. 
      inverts H8.
      2:go.
      rewrite TcbMod.set_a_get_a' in H9.
      2:go.
      unfolds in H4. destruct H4 as (Hhl1 & Hhl2 & Hhl3 & Hhl4).
      destruct H as [Hnul | Hhold].
      eapply Hhl2 in Hnul.
      simpljoin.
      intro.
      subst prio.
      eapply H5 in H9. destruct H9 as (Hnt & Hne).
      rewrite H4 in Hnt. inverts Hnt.
      eapply Hhl3 in Hhold.
      simpljoin.
      intro.
      subst prio.
      eapply H5 in H9. destruct H9 as (Hnt & Hne).
      rewrite H4 in Hnt. inverts Hnt. eapply Hne; eauto.
      rewrite TcbMod.set_a_get_a' in H8.
      2:go.
      assert ( tid' = tid \/ tid' <> tid) by tauto.
      destruct H11; intros.
      subst tid'.
      unfold get in *; simpl in *.
      rewrite TcbMod.set_a_get_a in H9.
      2:go.
      inverts H9.
      unfolds in H4. destruct H4 as (Hhl1 & Hhl2 & Hhl3 & Hhl4).
      destruct H as [Hnul | Hhold].
      eapply Hhl2 in Hnul.
      simpljoin.
      intro.
      subst prio.
      eapply H5 in H8. destruct H8 as (Hnt & Hne).
      rewrite H4 in Hnt. inverts Hnt.
      eapply Hhl3 in Hhold.
      simpljoin.
      intro.
      subst prio.
      eapply H5 in H8. destruct H8 as (Hnt & Hne).
      rewrite H4 in Hnt. inverts Hnt. eapply Hne; eauto.
      rewrite TcbMod.set_a_get_a' in H9.
      2: go.
      unfolds in  H6. 
      assert ( tid' <> tid0).
      unfolds. intros. eapply H7; eauto.
      eapply H3.
      2:{ eapply H8. }
      2:{ eapply H9. }
      eauto.
Qed.