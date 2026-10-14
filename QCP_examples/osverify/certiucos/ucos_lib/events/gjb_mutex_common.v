Require Import ucos_include.
Require Import os_ucos_h.
Require Import os_inv.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import mutex_pend_pure.
Require Import OSTimeTickPure.
Require Import gjb_common.
Require Import evheap_pure. (* new add *)
Require Import evaux_pure.
Require Import evt_spec_defs.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(* Definition PthreadMutex_full_P muxvl :=
forall i vl1, (0 <= i /\ i < Z.of_nat (length muxvl)) ->
                        nth_vallist (nat_of_Z i) muxvl = Some vl1 ->
                        ~(V_OSMUXINFOPevent vl1 = Some Vnull).

Definition nth_PthreadMutex_free_P i muxvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length muxvl) /\ 
                      nth_vallist (nat_of_Z i) muxvl = Some vl1 /\
                      V_OSMUXINFOPevent vl1 = Some Vnull. *)

Lemma Htmp:
forall x,
  Int.unsigned x <= 65535 ->
  Int.modu (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8) ($ Byte.modulus)
    = (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
Proof.
  intros.
  apply mund_int_a3 in H.
  remember (x&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  clear Heqi.
  unfold Int.modu.
  rewrite mund_int_byte_modulus.
  repeat ur_rewriter.
  apply mund_int_mod. auto.
Qed.

Lemma struct_type_vallist_match_hold:
forall vl v n,
 ( n< length vl )%nat ->
  n <> 8%nat ->
struct_type_vallist_match pthread_mutex_info_t vl->
struct_type_vallist_match pthread_mutex_info_t
  (update_nth_val n vl (Vint32 v)).
Proof. 
  intros.
  lets Hsp: struct_type_vallist_match_elim_10 H1.
  destruct Hsp.
  do 9 destruct H2.
  substs. 
  simpl in *.
  mytac.
  do 10 (try destruct n); simpl; try splits; eauto.
Qed.

Lemma length_vll_apthrmux: 
  forall s P minfol mcapl muxeibs ecbls vhold, 
    s |= AMuxEIBs minfol mcapl muxeibs ecbls vhold ** P ->
      length minfol = ∘ (OS_USER_MAX_EVENTS / 3). 
Proof.
  intros.
  unfold AMuxEIBs in *. 
  unfold APthreadMutex in *.
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpljoin1.
  auto.
Qed.

Lemma new_array_type_vallist_match_split1: 
  forall muxvl vll1 vll2 vl, 
    new_array_type_vallist_match pthread_mutex_info_t muxvl ->
    muxvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match pthread_mutex_info_t vll1 /\
      new_array_type_vallist_match pthread_mutex_info_t vll2 /\ 
      struct_type_vallist_match pthread_mutex_info_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.

Lemma muxb_corr': 
  forall vl vll1 vll2 minfob vhold v i, 
    EIBMAarray_P v (vll1 ++ vl :: vll2) minfob vhold ->
(*     EIBMAarray_P v (vll1 ++ vl :: vll2) minfob vhold -> *)
    Int.ltu i Int.zero = false -> 
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    (forall j, v = Vint32 j ->
               Int.ltu j Int.zero = false /\ Int.unsigned j + Int.unsigned i <= Int.max_unsigned) ->  
    exists j eid_t o x n pro pip w c mc, 
       v = Vint32 j /\
       get minfob (j +ᵢ i) = Some (eid_t, o, x, n, pro, pip, w, c, mc) /\
       (((eid_t = Null /\ V_OSMUXINFOPevent vl = Some Vnull) \/
       (eid_t = Holder /\ V_OSMUXINFOPevent vl = Some (Vptr vhold)) \/
 (exists eid,
  eid_t = Valid_Addr eid /\
  V_OSMUXINFOPevent vl = Some (Vptr eid) /\ eid <> vhold)) /\
((exists t opr,
 o = Some (t, opr) /\
 (Int.unsigned opr < 64 /\
 V_OSMUXINFOOwner vl = Some (Vint32 opr))) \/ 
 (o = None /\ V_OSMUXINFOOwner vl = Some (Vint32  (Int.repr OS_MUTEX_AVAILABLE)))) /\
V_OSMUXINFOType vl = Some (Vint32 x) /\
V_OSMUXINFORecursive_cnt vl = Some (Vint32 n) /\
V_OSMUXINFOPrio_ceiling vl = Some (Vint32 pip) /\
V_OSMUXINFOProtocol vl = Some (Vint32 pro) /\
V_OSMUXINFOWaitq_type vl = Some (Vint32 w) /\
V_OSMUXINFOCancel_safe vl = Some (Vint32 c) ).
Proof.
  inductions vll1.

  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  assert (Hiz: i = Int.zero).
  { 
    simpl in Hlen. destruct (Int.unsigned i) eqn: E.
    apply Int.unsigned_eq_zero; auto.
    int auto. int auto.
  }
  destruct Harrp as (v' & minfob' & pos & absminfob & Hv & Hjo & HP & Hv' & H').
  unfold RHL_EIBlk_Mux_P in HP.
  destruct absminfob as [[[[[[[[eo kd] i1] i2] i3] i4] i5] i6] i7].
  specialize (HP eo kd i1 i2 i3 i4 i5 i6 i7 (eq_refl _)).
  destruct v eqn: E; try inverts Hv.
  exists pos.
  exists eo kd i1 i2 i3.
  exists i4 i5 i6 i7.
  split; auto.
  split.
  assert (Heq: pos +ᵢ  i = pos). { rewrite Hiz. int auto. }
  rewrite Heq.
  eapply join_sig_get; eauto.
  auto. auto.

  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  simpl in Hlen.
  assert (Hige: Int.unsigned i >= 1). { auto with zarith. }
  destruct Harrp as (v' & minfob' & pos & absminfob & Hv & Hjo & HP & Hv' & H').
  eapply IHvll1 with (minfob:=minfob') (i:=Int.sub i ($1)) in H'; eauto.
  destruct H' as (j & eo & kd & i1 & i2 & i3 & i4 & i5 & i6 & i7 & H').
  exists pos eo kd i1 i2 i3.
  exists i4 i5 i6 i7.
  simpljoin1. splits; auto.
  inverts H.
  rewrite pos_add_sub_one in H0; auto.
  eapply join_lib.map_join_get_none' with (m2:=minfob'); eauto.
  apply get_a_sig_a'.
  specialize (Hsumrgn pos (eq_refl _)). 
  destruct Hsumrgn. apply pos_add_i_neq; auto.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.
  specialize (Hsumrgn pos (eq_refl _)).
  mytac.

  apply i_ge1_i_sub1_ge0. auto.
  int auto. int auto. 
  introv H_v'.
  subst v. subst v'. inverts H_v'.
  specialize (Hsumrgn pos (eq_refl _)).
  destruct Hsumrgn as (Hpos & Hadd).
  split. int auto. int auto.
  int auto. int auto. int auto.
Qed.

Lemma muxb_corr: 
  forall vl vll1 vll2 embls vhold i, 
    EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold  ->
(*     EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold -> *)
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    Int.ltu i Int.zero = false -> 
    Int.unsigned i <= Int.max_unsigned ->  
    exists eid_t o x n pro pip w c mc, 
      get embls i = Some (eid_t, o, x, n, pro, pip, w, c, mc) /\
        (((eid_t = Null /\
       V_OSMUXINFOPevent vl = Some Vnull) \/
      (eid_t = Holder /\
       V_OSMUXINFOPevent vl = Some (Vptr vhold)) \/
      (exists eid,
  eid_t = Valid_Addr eid /\
  V_OSMUXINFOPevent vl = Some (Vptr eid) /\ eid <> vhold)) /\
((exists t opr,
 o = Some (t, opr) /\
 (Int.unsigned opr < 64 /\
 V_OSMUXINFOOwner vl = Some (Vint32 opr))) \/ 
 (o = None /\ V_OSMUXINFOOwner vl = Some (Vint32  (Int.repr OS_MUTEX_AVAILABLE)))) /\
V_OSMUXINFOType vl = Some (Vint32 x) /\
V_OSMUXINFORecursive_cnt vl = Some (Vint32 n) /\
V_OSMUXINFOPrio_ceiling vl = Some (Vint32 pip) /\
V_OSMUXINFOProtocol vl = Some (Vint32 pro) /\
V_OSMUXINFOWaitq_type vl = Some (Vint32 w) /\
V_OSMUXINFOCancel_safe vl = Some (Vint32 c) ).
Proof.
  introv HP Hvll1 Hlt Hle.
  eapply muxb_corr' with (i:=i) in HP; eauto.
  2: {
    introv Hj0. 
    split. inv Hj0. int auto. inverts Hj0. int auto.
  }
  rewrite <- (Int.add_zero_l i).
  simpljoin1.
  do (* 7 *) 9 eexists. splits; eauto.
  instantiate (1:= x8).
  inverts H.
  auto.
Qed.

(* Require Import OSTimeTickPure.   *)
Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  rename H2 into Hpetbl; rename H3 into H2. (* new add *)
  destruct a; destruct p; simpljoin. (* add destruct p *)
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.

Lemma  RH_ECBlk_EIBlk_Mux_P_set_recurcnt:
forall els embls pos ei o z n pro pip w c mc n',
get embls pos = Some (ei, o, z, n, pro, pip, w, c, mc) ->
RH_ECBlk_EIBlk_Mux_P embls els  ->
RH_ECBlk_EIBlk_Mux_P (set embls pos (ei, o, z, n', pro, pip, w, c, mc)) els .
Proof.
  intros.
  funfold H0.
  unfolds.
  (* new add *)
  intros.
  rewrite MibMod.set_sem in *.
  destruct (idxspec.beq pos pos0) eqn: eq1.
  eapply idxspec.beq_true_eq in eq1; subst.
  inverts H1.
  eapply H0; eauto.
  eapply H0; eauto.
Qed.

Lemma  RH_ECBlk_EIBlk_Mux_P_set_owner:
forall els embls pos pip ei eid o ow z n pro pip' w c mc wl,
get embls pos = Some (ei, ow, z, n, pro, pip', w, c, mc) ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
RH_ECBlk_EIBlk_Mux_P embls els  ->
RH_ECBlk_EIBlk_Mux_P (set embls pos (ei, o, z, n, pro, pip', w, c, mc)) els .
Proof.
  intros.
  funfold H2.
  unfolds.
   (* new add *)
  introv Hget Heq.
  rewrite MibMod.set_sem in *.
  destruct (idxspec.beq pos pos0) eqn: eq1.
  eapply idxspec.beq_true_eq in eq1; subst.
  inverts Hget.
  eapply H2; eauto.
  eapply H2; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_recurcnt:
forall vl vhold cn cn' ei o x w pro pip c mc,
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 6 vl (Vint32 cn')) (ei, o, x, cn', pro, pip, w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
assert ((eid_t, o0, x0, cn, pro0, pip0, w0, c0, mc0) = (eid_t, o0, x0, cn, pro0, pip0, w0, c0, mc0)) by auto.
eapply H in H0.
clear H.
destruct H0 as (He & Hoe & Ht & Hcnt & Hpip & Hpro & Hwq); mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
destruct He as [He | [He | He]];mytac.
splits.
left. split;auto.
eapply nth_upd_neqrev. eauto. 
auto.
destruct Hoe as [How | Hno].
destruct How. destruct H.
destruct H1 as (Ho & Hlt & Hnt).
left.
exists x Ho.
splits; eauto.
destruct Hnt; eauto;
eapply nth_upd_neqrev. eauto. auto.
(* destruct Hno as (Ho & Hnt).
*)
eapply nth_upd_neqrev; eauto; auto.
destruct Hnt; eauto;
eapply nth_upd_neqrev.
right.
splits; auto.
destruct Hno; eauto.  
(* eapply update_nth. eauto. auto. *)
eapply nth_upd_neqrev. eauto. auto.
destruct Hno; auto.
eapply nth_upd_neqrev. eauto. auto.
eapply update_nth. eauto. auto.
eapply nth_upd_neqrev. eauto. auto. auto.
eapply nth_upd_neqrev; eauto.
eapply nth_upd_neqrev. eauto. auto. 
eapply nth_upd_neqrev. eauto; auto.
auto.  
splits.
right. left.
splits; auto.
eapply nth_upd_neqrev. eauto. auto.
destruct Hoe as [How | Hno].
destruct How. destruct H.
destruct H1 as (Ho & Hlt & Hnt).
left.
exists x Ho.
splits; eauto.
destruct Hnt; auto.
eapply nth_upd_neqrev. eauto. auto.
destruct Hnt; auto.
destruct Hno as (Ho & Hnt).
right.
splits; auto.
eapply nth_upd_neqrev; eauto; auto.
eapply nth_upd_neqrev. eauto. auto.
eapply update_nth. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
split.
right. right.
eexists.
splits; auto.
eapply nth_upd_neqrev. eauto. auto.
destruct Hoe as [How | Hno].
destruct How. 
split.
left.
destruct H1.
exists x1 x2.
destruct H1 as (Ho & Hlt & Hnt).
splits; eauto.
eapply nth_upd_neqrev. eauto. auto.
split.
eapply nth_upd_neqrev. eauto. auto.
split.
eapply update_nth. eauto. auto.
splits;
eapply nth_upd_neqrev; eauto; auto.
split. right; eauto.
splits; eauto. destruct Hno. auto.
eapply nth_upd_neqrev. eauto. auto.
destruct Hno. auto.
split. eapply nth_upd_neqrev. eauto. auto.
split. eapply update_nth. eauto. auto.
splits; eapply nth_upd_neqrev; eauto; auto.
Qed.


Lemma RHL_EIBlk_Mux_P_get_recurcnt:
forall vl x vhold,
RHL_EIBlk_Mux_P vl x vhold ->
exists v, V_OSMUXINFORecursive_cnt vl = Some v.
Proof.
intros.
funfold H.
destruct x as [[[[[[[[etp ow] mtp] cnt] prot] pip] wq] cans] mc].
assert ((etp, ow, mtp, cnt, prot, pip, wq, cans, mc)  = (etp, ow, mtp, cnt, prot, pip, wq, cans, mc)) by auto.
eapply H in H0.
destruct H0 as (_ & _ & _ & Hcnt & _ & _ & _ ); mytac.
Qed.

Lemma MibMod_get_join_sig_set:
forall  qls qid a qls1 b,
  MibMod.join (MibMod.sig qid b) qls1 qls ->
  MibMod.get qls1 qid = None ->
  MibMod.join (MibMod.sig qid a) qls1 (MibMod.set qls qid a).
Proof.
  intros.
  unfold MibMod.join.
  intros.
  rewrite MibMod.sig_sem.
  rewrite MibMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite MibMod.beq_refl.
  rewrite H0. auto.
  eapply idxspec.neq_beq_false in H1.
  rewrite H1.
  destruct (MibMod.get qls1 a0) eqn: eq2.
  lets Htg: MibMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (MibMod.get qls a0 = MibMod.get qls1 a0).
  eapply MibMod.map_join_get_none; try eauto.
  rewrite MibMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma MibMod_join_get_none_r :
 forall ma mb mc x a, 
      MibMod.get ma x = Some a -> 
      MibMod.join ma mb mc -> 
      MibMod.get mb x = None.
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (MibMod.get ma x).
  destruct (MibMod.get mb x).
  tryfalse.
  auto.
  destruct (MibMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma EIBMAarray_P_recurcnt_for_update_to_recurcnt:
forall vll1 vl vll2 embls e vhold pos j ei cn o x w pro c mc pip,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
V_OSMUXINFORecursive_cnt vl = Some (Vint32 cn) ->
EIBMAarray_P(* EIBMAarray_P *) (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P(* EIBMAarray_P *) (Vint32 j) 
                        (vll1 ++ (update_nth_val 6 vl (Vint32 e)) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, e, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H4.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H5.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
lets Hcp: H6.
eapply RHL_EIBlk_Mux_P_get_recurcnt in Hcp.
destruct Hcp. 
splits; eauto.
change ($ 0) with Int.zero.
instantiate (1:= (ei, o, x, e, pro, pip', w, c, mc)).
  2:{eapply RHL_EIBlk_Mux_P_set_recurcnt; eauto. }
change ($ 0) with Int.zero.
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H4. simpl.
mytac.
inverts H4.
do 4 eexists.
splits; eauto.
instantiate (1:= set x1 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) ((ei, o, x, e, pro, pip, w, c, mc))).
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. auto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H7. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H5.
erewrite H2 in H5.
rewrite H5.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_recurcnt_for_update_to_recurcnt':
forall vll1 vl vll2 embls ei n vhold pos o x w pro c mc cn pip,
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
V_OSMUXINFORecursive_cnt vl = Some (Vint32 cn) ->
EIBMAarray_P(* EIBMAarray_P *) (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P(* EIBMAarray_P *) (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 6 vl (Vint32 n)) :: vll2)
                        (set embls pos (ei, o, x, n, pro, pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_recurcnt_for_update_to_recurcnt in H3.
rewrite Int.add_zero in H3.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
 instantiate(1:=cn);auto.
rewrite Int.add_zero.
auto.
auto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_owner:
forall vl vhold cn ei eid o ow x w pro c mc els wl t pt pip pip',
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip ow, wl) ->
ow = Some (t, pt) ->
Int.unsigned pt < 64 ->
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip', w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 5 vl (Vint32 pt)) (ei, ow, x, cn, pro, pip', w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H4.
assert ((Valid_Addr eid, o, x0, n, pro0, pip0, w0, c0, mc0) = (Valid_Addr eid, o, x0, n, pro0, pip0, w0, c0, mc0)) by auto.
eapply H3 in H1.
clear H3.
destruct H1 as (He & Hoe & Ht & Hcnt & Hpro & Hpip & Hwq & Hcan); mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
destruct He as [He | [He | He]];mytac; tryfalse.
splits.
repeat right.
exists x.
split;auto.
split.
eapply nth_upd_neqrev. eauto. 
auto. auto.
destruct Hoe as [How | Hno].
destruct How. destruct H4.
destruct H4 as (Ho & Hlt & Hnt).
left.
exists t pt.
splits; eauto.
eapply update_nth; eauto.
destruct Hno as(Ho & Hnt).
left.
exists t pt.
splits; eauto. 
eapply update_nth; eauto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
Qed.

Lemma EIBMAarray_P_for_update_to_owner_y:
forall vll1 vl vll2 embls els eid pip wl vhold pos j ei cn o x w pro c mc t pt ow pip',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
o = Some (t, pt) -> 
Int.unsigned pt < 64 ->
MibMod.get embls (Int.add pos j)  = Some (ei, ow, x, cn, pro, pip', w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl (Vint32 pt)) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H7.
destruct x3 as [[[[[[[[etp own] mtp] cnt] prot] pip''] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H8.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H6.
rewrite H6 in Hget.
inverts Hget.
splits; eauto.
change ($ 0) with Int.zero.
  2:{eapply RHL_EIBlk_Mux_P_set_owner; eauto. }
change ($ 0) with Int.zero.
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H7. simpl.
mytac.
inverts H7.
do 4 eexists.
splits; eauto.
instantiate (1:= set x1 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) ((Valid_Addr eid, Some (t, pt), x, cn, pro, pip', w, c, mc))).
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. auto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H4. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H8.
erewrite H6 in H8.
rewrite H8.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_for_update_to_owner'_y:
forall vll1 vl vll2 embls ei vhold pos pip wl o x w pro c mc cn t pt eid els ow pip',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
o = Some (t, pt) ->
Int.unsigned pt < 64 ->
MibMod.get embls pos = Some (ei, ow, x, cn, pro, pip', w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 5 vl (Vint32 pt)) :: vll2)
                        (set embls pos (ei, o, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_for_update_to_owner_y in H6.
rewrite Int.add_zero in H6.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
 instantiate(1:=eid);auto.
eauto.
eauto.
eauto.
rewrite Int.add_zero.
eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_owner_n:
forall vl vhold cn ei eid o x w pro c mc els wl pip pip',
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip None, wl) ->
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip', w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE)))
                                 (ei, None, x, cn, pro, pip', w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H2.
assert ((Valid_Addr eid, o, x0, n, pro0, pip0, w0, c0, mc0) = (Valid_Addr eid, o, x0, n, pro0, pip0, w0, c0, mc0)) by auto.
eapply H1 in H.
clear H1.
destruct H as (He & Hoe & Ht & Hcnt & Hpro & Hpip & Hwq & Hcan ); mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
destruct He as [He | [He | He]];mytac; tryfalse.
splits.
repeat right.
exists x.
split;auto.
split.
eapply nth_upd_neqrev. eauto. 
auto. auto.
destruct Hoe as [How | Hno].
destruct How. destruct H3.
destruct H3 as (Ho & Hlt & Hnt).
right.
splits; eauto.
eapply update_nth; eauto.
destruct Hno as(Ho & Hnt).
right.
splits; eauto. 
eapply update_nth; eauto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
eapply nth_upd_neqrev. eauto. auto.
Qed.

Lemma EIBMAarray_P_for_update_to_owner_n:
forall vll1 vl vll2 embls els eid pip wl vhold pos j ei cn x w pro c mc ow pip',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip None, wl) ->
MibMod.get embls (Int.add pos j)  = Some (ei, ow, x, cn, pro, pip', w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE))) :: vll2)
                        (set embls (Int.add pos j) (ei, None, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H5.
destruct x3 as [[[[[[[[etp own] mtp] cnt] prot] pip''] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H6.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H4.
rewrite H4 in Hget.
inverts Hget.
splits; eauto.
change ($ 0) with Int.zero.
  2:{eapply RHL_EIBlk_Mux_P_set_owner_n; eauto. }
change ($ 0) with Int.zero.
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H5. simpl.
mytac.
inverts H5.
do 4 eexists.
splits; eauto.
instantiate (1:= set x1 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) ((Valid_Addr eid, None, x, cn, pro, pip', w, c, mc))).
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. auto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H5. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H6.
erewrite H4 in H6.
rewrite H6.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_for_update_to_owner'_n:
forall vll1 vl vll2 embls ei vhold pos pip wl x w pro c mc cn eid els ow pip',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip None, wl) ->
MibMod.get embls pos = Some (ei, ow, x, cn, pro, pip', w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE))) :: vll2)
                        (set embls pos (ei, None, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_for_update_to_owner_n in H4.
rewrite Int.add_zero in H4.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
 instantiate(1:=eid);auto.
eauto.
eauto.
eauto.
rewrite Int.add_zero.
eauto.
Qed.

Lemma PthreadMutex_full_imp_no_free
: forall muxvl,
    PthreadMutex_full_P muxvl ->
    ~(exists i, nth_PthreadMutex_free_P i muxvl).
Proof.
unfold nth_PthreadMutex_free_P.
unfold PthreadMutex_full_P.
intros.
do 2 (eapply Classical_Pred_Type.all_not_not_ex; intros).
pure_auto.
Qed.

Lemma PthreadMutex_free_imp_no_full
: forall muxvl,
    (exists i, nth_PthreadMutex_free_P i muxvl) ->
     ~(PthreadMutex_full_P muxvl).
Proof.
unfold nth_PthreadMutex_free_P.
unfold PthreadMutex_full_P.
intros.
pure_auto.
do 3 destruct H.
destruct H1.
destruct H2.
eapply H0; eauto.
Qed.


Lemma PthreadMutex_free_dec
: forall muxvl,
    (exists i, nth_PthreadMutex_free_P i muxvl) \/ PthreadMutex_full_P muxvl.
Proof.
intros.
assert (Ht: (PthreadMutex_full_P muxvl) \/ ~(PthreadMutex_full_P muxvl)) by tauto.
destruct Ht. pure_auto.
left.
unfold nth_PthreadMutex_free_P in *.
unfold PthreadMutex_full_P in *.
eapply Classical_Pred_Type.not_all_ex_not in H.
destruct H.
eapply Classical_Pred_Type.not_all_ex_not in H.
destruct H.
eapply Classical_Prop.imply_to_and in H; destruct H.
eapply Classical_Prop.imply_to_and in H0; destruct H0.
destruct H.
repeat eexists; eauto.
tauto.
Qed.

Lemma APthreadMutex_select_sn_ex_strong_frm:
  forall s b i muxvl,
     s |= EX vll1 n vll2 (* b i *) vl ,
             GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray pthread_mutex_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen pthread_mutex_info_t)))) pthread_mutex_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen pthread_mutex_info_t))))
               (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
             [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| muxvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] ->
    s |= APthreadMutex (b, i) muxvl.
Proof.
  intros.
  apply astar_r_aemp_elim.
  eapply APthreadMutex_select_sn_ex_strong.
  sep auto.
Qed.

Lemma PthreadMutex_full_P_nil :
PthreadMutex_full_P nil.
Proof.
unfold PthreadMutex_full_P.
simpl. auto with zarith.
Qed.

Lemma PthreadMutex_full_P_succ :
forall a vl, PthreadMutex_full_P (a :: vl) <-> (PthreadMutex_full_P (a::nil) /\PthreadMutex_full_P vl).
Proof.
unfold PthreadMutex_full_P.
(* simpl. *)
split; intros.
simpl in *.
split; intros.
eapply H. instantiate (1:= i). int auto.
destruct (∘ i); tryfalse. auto.
eapply H. instantiate (1:= (i + 1)). int auto.
assert (Hi: (∘ (i + 1)) = ((∘ i) + (∘ 1))%nat).
eapply nat_of_Z_plus; auto with zarith.
rewrite Hi.
change (∘ 1) with 1%nat.
assert (Hi': (∘ i + 1)%nat = S (∘ i)).
auto with zarith.
rewrite Hi'. auto.
destruct H.
destruct H0.
assert (Hi: i= 0 \/ i <> 0) by tauto.
(* simpl in *. *)
destruct Hi.
eapply H. simpl in *. eauto with zarith. subst i. auto.
eapply H2. instantiate (1:= i - 1). simpl in *. eauto with zarith.
assert (Hsub: i = i - 1 +1).
rewrite Z.sub_add. auto.
rewrite Hsub in H1.
assert (Hi: ∘ (i - 1 + 1) = ((∘ (i - 1)) + (∘ 1))%nat).
eapply nat_of_Z_plus; auto with zarith.
rewrite Hi in H1.
change (∘ 1) with 1%nat in H1.
assert (Hi': (∘ (i - 1) + 1)%nat = S (∘ (i - 1))) by auto with zarith.
rewrite Hi' in H1.
simpl in H1. auto.
Qed.

Lemma PthreadMutex_full_P_split:
forall vl1 vl2, (PthreadMutex_full_P vl1 /\ PthreadMutex_full_P vl2)  <-> PthreadMutex_full_P (vl1 ++ vl2).
Proof.
induction vl1; intros.
simpl. split; try pure_auto. apply PthreadMutex_full_P_nil.
simpl.
rewrite PthreadMutex_full_P_succ.
rewrite PthreadMutex_full_P_succ with (vl:= vl1 ++ vl2).
rewrite <- IHvl1.
tauto.
Qed.

Lemma APthreadMutex_split: 
  forall s b i vll1 vl vll2,
    s |= APthreadMutex (b, i) (vll1 ++ (vl :: vll2)) ->
    s |= EX idx (* b i *),
           GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray pthread_mutex_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen pthread_mutex_info_t))) pthread_mutex_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen pthread_mutex_info_t))))
          (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match pthread_mutex_info_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof.
intros.
unfold APthreadMutex in H.
(* destruct H.
destruct x. *)
sep lift 2%nat in H.
sep split in H.
destruct H0.
lets Hl: H1.
rewrite app_length in Hl.
rewrite <- Hl in H.
assert ((length vll1 < ∘ (OS_USER_MAX_EVENTS / 3))%nat).
rewrite <- Hl. simpl.
auto with zarith.
assert (Hl2: length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1)))).
{
  unfold nat_of_Z in *.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1))) =
                  (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
  eapply Z2Nat.inj_sub; auto with zarith.
  rewrite H3.
  rewrite <- Hl.
  rewrite Nat2Z.id.
  simpl.
  auto with zarith.
}
eapply Aarray_new_split_strong_frm in H; try (split; auto).
2: { unfold sem_info_t. simpl typelen.
     (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
     lets Hrgn: usr_max_evts_rgn.
     destruct Hrgn as (Hrgn3 & Hrgn4).
     clear -H2 Hrgn3 Hrgn4.
     unfold nat_of_Z in H2.
     int auto. }
sep pauto.
sep cancel 1%nat 1%nat.
change (length (vl :: vll2)) with (S (length vll2)) in H.
eapply Aarray_new_succ_imp in H.
rewrite Int.add_assoc in H.
assert (Hsuc: ($ Z.of_nat (length vll1 * typelen pthread_mutex_info_t) +ᵢ
          $ Z.of_nat (typelen pthread_mutex_info_t)) =
     $ Z.of_nat (S (length vll1) * typelen pthread_mutex_info_t) ).
{
  clear -Hl H2.
  unfold pthread_mutex_info_t. simpl typelen.
  assert ((S (length vll1) * 64)%nat = ((((length vll1) * 64)%nat + 64)%nat)).
  auto with zarith.
  rewrite H.
  rewrite Nat2Z.inj_add.
  (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  clear -H2 Hrgn3 Hrgn4.
  unfold nat_of_Z in H2.
  int auto.
}
rewrite Hsuc in H.
rewrite <- Hl2.
sep cancel 2%nat 2%nat.
unfold Aarray_new in H.
unfold Aarray_new' in H. unfold pthread_mutex_info_t in H.
fold pthread_mutex_info_t in H.
sep pauto.
(* change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat in H2. *)
(* change (OS_USER_MAX_EVENTS / 3) with 6. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
clear -H2 Hrgn3 Hrgn4.
unfold nat_of_Z in H2.
auto with zarith.
Qed. 

Lemma APthreadMutex_split_frm: 
  forall s b i vll1 vl vll2 P,
    s |= APthreadMutex (b, i) (vll1 ++ (vl :: vll2)) ** P ->
    s |= EX idx (* b i *),
           GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray pthread_mutex_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen pthread_mutex_info_t))) pthread_mutex_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen pthread_mutex_info_t))))
          (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match pthread_mutex_info_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |] ** P.  
Proof.
intros.
unfold APthreadMutex in H.
sep normal in H.
(* destruct H.
destruct x. *)
sep lift 2%nat in H.
sep split in H.
destruct H0.
lets Hl: H1.
rewrite app_length in Hl.
rewrite <- Hl in H.
assert ((length vll1 < ∘ (OS_USER_MAX_EVENTS / 3))%nat).
rewrite <- Hl. simpl.
auto with zarith.
assert (Hl2: length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1)))).
{
  unfold nat_of_Z in *.
  assert (Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (length vll1))) =
                  (Z.to_nat (OS_USER_MAX_EVENTS / 3) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
  eapply Z2Nat.inj_sub; auto with zarith.
  rewrite H3.
  rewrite <- Hl.
  rewrite Nat2Z.id.
  simpl.
  auto with zarith.
}
eapply Aarray_new_split_strong_frm in H; try (split; auto).
2: { unfold sem_info_t. simpl typelen.
     (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
     lets Hrgn: usr_max_evts_rgn.
     destruct Hrgn as (Hrgn3 & Hrgn4).
     clear -H2 Hrgn3 Hrgn4.
     unfold nat_of_Z in H2.
     int auto. }
sep pauto.
sep cancel 1%nat 1%nat.
change (length (vl :: vll2)) with (S (length vll2)) in H.
eapply Aarray_new_succ_imp in H.
rewrite Int.add_assoc in H.
assert (Hsuc: ($ Z.of_nat (length vll1 * typelen pthread_mutex_info_t) +ᵢ
          $ Z.of_nat (typelen pthread_mutex_info_t)) =
     $ Z.of_nat (S (length vll1) * typelen pthread_mutex_info_t) ).
{
  clear -Hl H2.
  unfold pthread_mutex_info_t. simpl typelen.
  assert ((S (length vll1) * 64)%nat = ((((length vll1) * 64)%nat + 64)%nat)).
  auto with zarith.
  rewrite H.
  rewrite Nat2Z.inj_add.
  (* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in H2. *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  clear -H2 Hrgn3 Hrgn4.
  unfold nat_of_Z in H2.
  int auto.
}
rewrite Hsuc in H.
rewrite <- Hl2.
sep cancel 2%nat 2%nat.
unfold Aarray_new in H.
unfold Aarray_new' in H. unfold pthread_mutex_info_t in H.
fold sem_info_t in H.
sep pauto.
(* change (∘ (OS_USER_MAX_EVENTS / 3)) with 6%nat in H2.
change (OS_USER_MAX_EVENTS / 3) with 6. *)
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
clear -H2 Hrgn3 Hrgn4.
unfold nat_of_Z in H2.
auto with zarith.
Qed.

Lemma new_array_type_vallist_match_mux_getp:
forall vll1 vl vll2,
new_array_type_vallist_match pthread_mutex_info_t (vll1 ++ (vl :: vll2)) ->
exists v, V_OSMUXINFOPevent vl = Some v /\ isptr v.
Proof.
intros.
eapply new_array_type_vallist_match_split1 in H; eauto.
destruct H as (_ & _ & Hsp).
lets Hvl: struct_type_vallist_match_elim_10 Hsp.
destruct Hvl. do 9 destruct H.
subst vl.
simpl in Hsp.
destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & Hk & _).
exists x3.
unfold V_OSMUXINFOPevent. unfold isptr.
simpl. split; auto.
destruct x3; tryfalse; pure_auto.
Qed.

(* some Ltac *)

Ltac mytac_lift_absop :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_aop P with
            | none _ => idtac 1 "no absop in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac mytac_lift_abmuxbls :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P absmutinfoid with
            | none _ => idtac 1 "no abmuxbls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac mytac_lift_abecbls :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P absecblsid with
            | none _ => idtac 1 "no abecbls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac mytac_lift_abtcbls :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P abstcblsid with
            | none _ => idtac 1 "no abtcbls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac mytac_lift_curt :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P curtid with
            | none _ => idtac 1 "no curt in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Lemma RH_EIB_ECB_Q_P_mux_set_preserve: 
  forall els qeibs sid  pip pip' o o' wls wls', 
    RH_EIBlk_ECBlk_Q_P els qeibs -> 
    get els sid = Some (absmutexsem pip o, wls) ->
    RH_EIBlk_ECBlk_Q_P (set els sid (absmutexsem pip' o', wls')) qeibs. 
Proof.
  introv Hrh Hget.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
  - rewrite join_lib.set_a_get_a'; eauto. 
Qed.

Lemma RH_SEM_EINFO_ECB_P_mux_set_preserve : 
  forall els sid embls pip pip' o o' wls wls',
    RH_SEM_EINFO_ECB_P els embls ->
    EcbMod.get els sid = Some (absmutexsem pip o, wls) ->
    RH_SEM_EINFO_ECB_P (set els sid (absmutexsem pip' o', wls')) embls.
Proof.
  introv Hrh Hget.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget'.
  casetac sid eid Ht Hf.
  - subst.
    lets H00: Hrh Hget'.
    simpljoin1.
    unfold get in *; unfold EcbMap,EmbMap in*.
    rewrite Hget in H.
    inverts H.
  - rewrite join_lib.set_a_get_a'; eauto. 
Qed.

Lemma RH_MUX_EIB_ECB_P_mux_set_preserve:
  forall muxeibs els sid pip pip' o o' wls wls',
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    EcbMod.get els sid = Some (absmutexsem pip o, wls) ->
    RH_ECBlk_EIBlk_Mux_P muxeibs (set els sid (absmutexsem pip' o', wls')). 
Proof.
  introv Hrh Hget.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget' Htpeq.
  subst eid_tp.
  casetac sid eid Ht Hf.
  -
    subst.
    lets H00: Hrh Hget'.
    specialize (H00 (eq_refl _)).
    simpljoin1.
    rewrite join_lib.set_a_get_a; eauto.
  -
    rewrite join_lib.set_a_get_a'; eauto.
Qed.

Lemma apthreadmutex_len_frm: 
  forall s l vl P, s |= APthreadMutex l vl ** P -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  unfold APthreadMutex.
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.

Lemma muxb_corr_alt: 
  forall i muxvl embls vhold, 
    EIBMAarray_P (Vint32 Int.zero) muxvl embls vhold ->
    (i < (length muxvl))%nat ->
    length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl eid_t o x n pro pip w c mc, 
      nth_vallist i muxvl = Some vl /\
        get embls ($ (Z.of_nat i)) = Some (eid_t, o, x, n, pro, pip, w, c, mc) /\
        (((eid_t = Null /\
       V_OSMUXINFOPevent vl = Some Vnull) \/
      (eid_t = Holder /\
       V_OSMUXINFOPevent vl = Some (Vptr vhold)) \/
      (exists eid,
             eid_t = Valid_Addr eid /\
            V_OSMUXINFOPevent vl = Some (Vptr eid) /\ eid <> vhold)) /\
          ((exists t opr,
                o = Some (t, opr) /\
              (Int.unsigned opr < 64 /\
                 V_OSMUXINFOOwner vl = Some (Vint32 opr))) \/ 
            (o = None /\ V_OSMUXINFOOwner vl = Some (Vint32  (Int.repr OS_MUTEX_AVAILABLE)))) /\
            V_OSMUXINFOType vl = Some (Vint32 x) /\
            V_OSMUXINFORecursive_cnt vl = Some (Vint32 n) /\
            V_OSMUXINFOPrio_ceiling vl = Some (Vint32 pip) /\
            V_OSMUXINFOProtocol vl = Some (Vint32 pro) /\
            V_OSMUXINFOWaitq_type vl = Some (Vint32 w) /\
            V_OSMUXINFOCancel_safe vl = Some (Vint32 c) ). 
Proof.
introv He Hi Hl.
destruct muxvl.
simpl in *. false.
auto with zarith.
assert (v :: muxvl <> nil ) by eauto.
lets Hsp: list_vallist_split_idx Hi H.
destruct Hsp. do 3 destruct H0.
rewrite H0 in *.
eapply muxb_corr in He.
instantiate (1:= ($ Z.of_nat i)) in He.
mytac.
repeat eexists; pauto.
rewrite nth_vallist_get_idx. auto.
subst i.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in Hi.
int auto.
rewrite int_ltu_zero_eq_false; auto.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in Hi.
int auto.
Qed.

Lemma muxb_corr_alt': 
  forall i muxvl embls vhold, 
    EIBMAarray_P (Vint32 Int.zero) muxvl embls vhold ->
    (Int.unsigned i) < Z.of_nat (length muxvl) ->
    length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists vl eid_t o x n pro pip w c mc, 
      nth_vallist ∘ (Int.unsigned i) muxvl = Some vl /\
        get embls i = Some (eid_t, o, x, n, pro, pip, w, c, mc) /\
        (((eid_t = Null /\
       V_OSMUXINFOPevent vl = Some Vnull) \/
      (eid_t = Holder /\
       V_OSMUXINFOPevent vl = Some (Vptr vhold)) \/
      (exists eid,
             eid_t = Valid_Addr eid /\
            V_OSMUXINFOPevent vl = Some (Vptr eid) /\ eid <> vhold)) /\
          ((exists t opr,
                o = Some (t, opr) /\
              (Int.unsigned opr < 64 /\
                 V_OSMUXINFOOwner vl = Some (Vint32 opr))) \/ 
            (o = None /\ V_OSMUXINFOOwner vl = Some (Vint32  (Int.repr OS_MUTEX_AVAILABLE)))) /\
            V_OSMUXINFOType vl = Some (Vint32 x) /\
            V_OSMUXINFORecursive_cnt vl = Some (Vint32 n) /\
            V_OSMUXINFOPrio_ceiling vl = Some (Vint32 pip) /\
            V_OSMUXINFOProtocol vl = Some (Vint32 pro) /\
            V_OSMUXINFOWaitq_type vl = Some (Vint32 w) /\
            V_OSMUXINFOCancel_safe vl = Some (Vint32 c) ). 
Proof.
introv He Hi Hl.
eapply muxb_corr_alt in He.
instantiate (1:= ∘ (Int.unsigned i)) in He.
assert (($ Z.of_nat ∘ (Int.unsigned i)) = i).
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in Hi.
unfold nat_of_Z in *.
assert (Z.of_nat (Z.to_nat (Int.unsigned i)) = Int.unsigned i).
apply Z2Nat.id.
int auto.
rewrite H.
apply Int.repr_unsigned.
rewrite H in He.
auto.
unfold nat_of_Z in *.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn3 & Hrgn4).
(* change ∘ (OS_USER_MAX_EVENTS / 3) with 6%nat in Hl. *)
rewrite Hl in *.
int auto.
auto.
Qed.

Lemma muxb_get_not_null: 
  forall muxvl embls hld, 
    EIBMAarray_P (Vint32 Int.zero) muxvl embls hld ->
    PthreadMutex_full_P muxvl ->
    length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
    ~(exists pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc0,
                    MibMod.get embls pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc0) /\
                      0 <= Int.unsigned pos < Z.of_nat (length muxvl)).
Proof.
introv He Hf Hl.
funfold Hf.
introv H.
mytac.
eapply muxb_corr_alt' in He; eauto.
mytac.
unfold get in *; unfold MibMap in *.
rewrite H3 in H; inverts H.
destruct H4.
destruct H.
eapply Hf; eauto.
destruct H. destruct H. tryfalse. 
destruct H. destruct H. tryfalse.
Qed.

Lemma muxb_getnull:
  forall vl vll1 vll2 embls hld i,
    EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls hld ->
    nth_PthreadMutex_free_P i (vll1 ++ vl :: vll2) ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2)  = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists ow tp rcnt prot0 prioc0 wq0 cnsa0 mc0,
                    MibMod.get embls (Int.repr i) = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc0) /\
                      V_OSMUXINFOPevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  rewrite Hl2 in H0.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  unfold nat_of_Z in H0.
  assert (Z.of_nat (Z.to_nat (OS_USER_MAX_EVENTS / 3)) = (OS_USER_MAX_EVENTS / 3)).
  apply Z2Nat.id.
  int auto.
  rewrite H3 in H0.
  assert (Hi_ran: Int.ltu ($ i) Int.zero = false /\ Int.unsigned ($ i) <= Int.max_unsigned).
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  destruct Hi_ran as (Hi1 & Hi2).
  assert (Hi: Int.unsigned (Int.repr i) = i).
  eapply int_usign_eq; auto.
  (* change (OS_USER_MAX_EVENTS / 3) with 6 in H0. *)
  int auto.
  unfold nat_of_Z in H1.
  rewrite <- Hl1 in H1.
  rewrite nth_vallist_get_idx in H1.
  inverts H1.
  rewrite <- Hi in Hl1.
  lets Hmux: muxb_corr He Hl1 Hi1 Hi2.
  mytac.
  unfold V_OSMUXINFOPevent in *.
  rewrite Hi in Hl1.
  rewrite H2 in H4.
  do 2 destruct H4; mytac; tryfalse.
  repeat eexists.
  apply H1.
  auto.
Qed.

Lemma RH_ECBlk_EIBlk_Mux_P_set_to_hold:
  forall els embls pos ow tp rcnt prot prioc wq cnsa mc,
    RH_ECBlk_EIBlk_Mux_P embls els ->
    RH_ECBlk_EIBlk_Mux_P (set embls pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) els. 
Proof.
  unfold RH_ECBlk_EIBlk_Mux_P.
  intros.
  rewrite MibMod.set_sem in H0.
  destruct (idxspec.beq pos pos0) eqn: eq1; tryfalse.
  eapply H in H0; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_hold:
forall vl vhold cn ei o x w pro pip c mc,
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 8 vl (Vptr vhold)) (Holder, o, x, cn, pro, pip, w, c,mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
right. left.
split; auto.
destruct H as [H | [H | H]];mytac;
eapply update_nth; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_hold:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 8 vl (Vptr vhold)) :: vll2)
                        (set embls (Int.add pos j) (Holder, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_hold; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_hold':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip,
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 8 vl (Vptr vhold)) :: vll2)
                        (set embls pos (Holder, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_hold in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_null:
forall vl vhold cn ei o x w pro pip c mc,
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 8 vl Vnull) (Null, o, x, cn, pro, pip, w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
left.
split; auto.
destruct H as [H | [H | H]];mytac;
eapply update_nth; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_null:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 8 vl (Vnull)) :: vll2)
                        (set embls (Int.add pos j) (Null, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_null; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_null':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip,
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 8 vl (Vnull)) :: vll2)
                        (set embls pos (Null, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_null in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_ptr:
forall vl vhold cn ei o x w pro pip c mc eid,
eid <> vhold ->
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 8 vl (Vptr eid)) (Valid_Addr eid, o, x, cn, pro, pip, w, c, mc) vhold.
Proof.
introv Hneq.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
right.  right.
repeat eexists; eauto.
destruct H as [H | [H | H]];mytac;
eapply update_nth; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_ptr:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip eid,
eid <> vhold ->
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 8 vl (Vptr eid)) :: vll2)
                        (set embls (Int.add pos j) (Valid_Addr eid, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; introv Hneq; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_ptr; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_ptr':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip eid,
eid <> vhold ->
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 8 vl (Vptr eid)) :: vll2)
                        (set embls pos (Valid_Addr eid, o, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
introv Hneq. intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_ptr in H2.
rewrite Int.add_zero in H2.
eauto. auto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_cancel:
forall vl vhold cn ei o x w pro pip c mc c',
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 4 vl (Vint32 c')) (ei, o, x, cn, pro, pip, w, c', mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
eapply update_nth; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_protocol:
forall vl vhold cn ei o x w pro pip c mc pro',
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 1 vl (Vint32 pro')) (ei, o, x, cn, pro', pip, w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
eapply update_nth; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_owner_none:
forall vl vhold cn ei o x w pro pip c mc,
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE))) (ei, None, x, cn, pro, pip, w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _ (eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
right.
splits; auto.
destruct H0 as [H0 | H0]; mytac.
eapply update_nth; eauto.
eapply update_nth; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_type:
forall vl vhold cn ei o x w pro pip c mc x',
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 0 vl (Vint32 x')) (ei, o, x', cn, pro, pip, w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _(eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
eapply update_nth; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_prioceiling:
forall vl vhold cn ei o x w pro pip c mc pip',
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 2 vl (Vint32 pip')) (ei, o, x, cn, pro, pip', w, c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _(eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
eapply update_nth; eauto.
Qed.

Lemma RHL_EIBlk_Mux_P_set_waitq:
forall vl vhold cn ei o x w pro pip c mc w',
RHL_EIBlk_Mux_P vl (ei, o, x, cn, pro, pip, w, c, mc) vhold ->
RHL_EIBlk_Mux_P (update_nth_val 3 vl (Vint32 w')) (ei, o, x, cn, pro, pip, w', c, mc) vhold.
Proof.
unfold RHL_EIBlk_Mux_P.
intros.
inverts H0.
specialize (H _ _ _ _ _ _ _ _ _(eq_refl _)).
mytac.
unfold V_OSMUXINFOPevent in *.
unfold V_OSMUXINFOOwner in *.
unfold V_OSMUXINFOType in *.
unfold V_OSMUXINFORecursive_cnt in *.
unfold V_OSMUXINFOPrio_ceiling in *.
unfold V_OSMUXINFOProtocol in *.
unfold V_OSMUXINFOWaitq_type in *.
unfold V_OSMUXINFOCancel_safe in *.
splits; try (eapply nth_upd_neqrev; eauto; fail).
destruct H as [H | [H | H]];mytac;
[left | right; left | right; right];
try splits; try repeat eexists; eauto;
try eapply nth_upd_neqrev; eauto.
destruct H0 as [H0 | H0]; mytac.
left. repeat eexists; eauto.
eapply nth_upd_neqrev; eauto.
right. splits; auto.
eapply nth_upd_neqrev; eauto.
eapply update_nth; eauto.
Qed.


Lemma EIBMAarray_P_hold_for_update_to_cancel:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip c',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 4 vl (Vint32 c')) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, cn, pro, pip, w, c', mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_cancel; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_cancel':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip c',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 4 vl (Vint32 c')) :: vll2)
                        (set embls pos (ei, o, x, cn, pro, pip, w, c', mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_cancel in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.


Lemma EIBMAarray_P_hold_for_update_to_protocol:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip pro',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 1 vl (Vint32 pro')) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, cn, pro', pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_protocol; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_protocol':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip pro',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 1 vl (Vint32 pro')) :: vll2)
                        (set embls pos (ei, o, x, cn, pro', pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_protocol in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_owner_none:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip,
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE))) :: vll2)
                        (set embls (Int.add pos j) (ei, None, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_owner_none; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_owner_none':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip,
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 5 vl (Vint32 (Int.repr OS_MUTEX_AVAILABLE))) :: vll2)
                        (set embls pos (ei, None, x, cn, pro, pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_owner_none in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_prioceiling:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip pip',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 2 vl (Vint32 pip')) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip0] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_prioceiling; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_prioceiling':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip pip',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 2 vl (Vint32 pip')) :: vll2)
                        (set embls pos (ei, o, x, cn, pro, pip', w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_prioceiling in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_type:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip x',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 0 vl (Vint32 x')) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x', cn, pro, pip, w, c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_type; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_type':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip x',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 0 vl (Vint32 x')) :: vll2)
                        (set embls pos (ei, o, x', cn, pro, pip, w, c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_type in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_waitq:
forall vll1 vl vll2 embls vhold pos j ei cn o x w pro c mc pip w',
pos = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned j + Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls (Int.add pos j)  = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 j) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 j) 
                        (vll1 ++ (update_nth_val 3 vl (Vint32 w')) :: vll2)
                        (set embls (Int.add pos j) (ei, o, x, cn, pro, pip, w', c, mc)) vhold.
Proof.
induction vll1; intros.
simpl in *.
mytac.
inverts H3.
destruct x3 as [[[[[[[[etp ow] mtp] cnt] prot] pip'] wq] cans] mc'].
do 4 eexists.
lets Hget: MibMod.join_sig_get H4.
change ($ 0) with Int.zero in *.
rewrite Int.add_zero_l in H2.
rewrite H2 in Hget.
inverts Hget.
splits; eauto.
2: { eapply RHL_EIBlk_Mux_P_set_waitq; eauto. }
rewrite Int.add_zero_l.
eapply MibMod_get_join_sig_set; eauto.
eapply MibMod_join_get_none_r; [idtac | eauto].
eapply MibMod.map_get_sig.
(* case 2 *)
assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
eapply int_usign_eq; simpl length in *; auto with zarith.
assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
eapply int_usign_eq; simpl length in *; auto with zarith.
simpl in H3. simpl.
mytac.
inverts H3.
do 4 eexists.
splits; eauto.
eapply MibMod.join_comm.
eapply MibMod.map_join_set_none.
eapply MibMod.join_comm. eauto.
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x2) 
                = ($ Z.of_nat (length vll1) +ᵢ  (x2 +ᵢ  Int.one))).
rewrite Int.add_permut.
rewrite Int.add_commut.
int auto; simpl length in *; auto with zarith.
int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
rewrite Heq.
eapply IHvll1; eauto.
simpl length in *; auto with zarith.
rewrite Heq1 in H1.
simpl length in H1.
assert (Int.unsigned x2 + Z.of_nat (S (length vll1)) = (Int.unsigned x2 + 1) + Z.of_nat (length vll1)).
auto with zarith.
rewrite H in H1.
assert (0 <= Int.unsigned x2 + 1).
pose proof (Int.unsigned_range_2 x2).
auto with zarith.
lets Hcp: H1.
eapply Z_add_le_trans in Hcp; auto with zarith.
assert (Int.unsigned (x2 +ᵢ  Int.one) = Int.unsigned x2 + 1).
int auto;simpl length in *; auto with zarith.
rewrite H6. rewrite Heq2. auto.
eapply MibMod.map_join_get_none in H4.
erewrite H2 in H4.
rewrite H4.
rewrite Heq. auto. 
eapply MibMod.get_sig_none.
rewrite Int.add_commut.
eapply pos_add_i_neq. rewrite Heq1.
simpl length in *; auto with zarith.
rewrite int_ltu_zero_eq_false; auto.
auto.
Qed.

Lemma EIBMAarray_P_hold_for_update_to_waitq':
forall vll1 vl vll2 embls ei vhold pos o x w pro c mc cn pip w',
length vll1 = Z.to_nat (Int.unsigned pos) ->
0 <= Int.unsigned pos <= Int.max_unsigned ->
MibMod.get embls pos = Some (ei, o, x, cn, pro, pip, w, c, mc) ->
EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls vhold ->
EIBMAarray_P (Vint32 Int.zero) 
                       (vll1 ++ (update_nth_val 3 vl (Vint32 w')) :: vll2)
                        (set embls pos (ei, o, x, cn, pro, pip, w', c, mc)) vhold.
Proof.
intros.
 lets Hr: Int.unsigned_repr H0. 
destruct H0.
eapply EIBMAarray_P_hold_for_update_to_waitq in H2.
rewrite Int.add_zero in H2.
eauto.
eapply Z2Nat.id in H0.
rewrite H.
rewrite H0.
rewrite Int.repr_unsigned; auto.
  rewrite H.
eapply Z2Nat.id in H0.
rewrite H0. auto.  
rewrite Int.unsigned_zero. 
auto with zarith.
rewrite Int.add_zero.
eauto.
Qed.

(* used for pthread mutex destroy *)

Lemma sem_eib_ecb_delmux_preserve: 
  forall semeibs ecbls i1 ecbls' eid o, 
    RH_SEM_EINFO_ECB_P ecbls semeibs ->
    join ecbls' (sig eid (absmutexsem i1 o, nil)) ecbls ->
    ~semeib_ref semeibs eid ->
    RH_SEM_EINFO_ECB_P ecbls' semeibs. 
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hgetpos.
  casetac eid0 eid Heq Hneq.
  subst.
  unfold semeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos. clear Heibecb.
  simpljoin1.
  exists x x0.
  assert (join (sig eid (absmutexsem i1 o, nil)) ecbls' ecbls).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma asemeib_delmux_preserve: 
  forall s ecbls ecbls' eid i1 infol scapl semeibs vhold P o, 
    s |= ASemEIBs infol scapl semeibs ecbls vhold ** P -> 
    join ecbls' (sig eid (absmutexsem i1 o, nil)) ecbls ->
    ~semeib_ref semeibs eid ->
    s |= ASemEIBs infol scapl semeibs ecbls' vhold ** P.  
Proof.
  introv Hsat Hjo Hnref.
  unfold ASemEIBs in *.
  sep pauto.
  eapply sem_eib_ecb_delmux_preserve; eauto.
Qed.

Lemma mq_eib_ecb_delmux_preserve:
  forall mqeibs ecbls i1 ecbls' eid o, 
    RH_EIBlk_ECBlk_Q_P ecbls mqeibs -> 
     join ecbls' (sig eid (absmutexsem i1 o, nil)) ecbls  ->
    ~mqeib_ref mqeibs eid ->
    RH_EIBlk_ECBlk_Q_P ecbls' mqeibs.
Proof.
  introv Heibecb Hjo Hnref.
  unfold RH_EIBlk_ECBlk_Q_P in *. 
  introv Hgetpos. 
  casetac eid0 eid Heq Hneq.
  subst.
  unfold mqeib_ref in Hnref.
  false. apply Hnref. repeat eexists. eauto.
  lets H00: Heibecb Hgetpos. clear Heibecb.
  simpljoin1.
  exists x x0 x1 x2.
  assert (join (sig eid (absmutexsem i1 o, nil)) ecbls' ecbls).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed. 

Lemma mqeib_delmux_preserve: 
  forall s qattrl qcapl mqeibs ecbls ecbls' vhold eid i1 P o, 
    s |= AMqEIBs qattrl qcapl mqeibs ecbls vhold ** P ->  
    join ecbls' (sig eid (absmutexsem i1 o, nil)) ecbls ->
    ~mqeib_ref mqeibs eid ->
    s |= AMqEIBs qattrl qcapl mqeibs ecbls' vhold ** P. 
Proof.
  introv Hsat Hjo Hnref.
  unfold AMqEIBs in *.
  sep pauto.
  eapply mq_eib_ecb_delmux_preserve; eauto.
Qed.

Lemma mux_einfo_ecb_delmux_preserve: 
  forall els semeibs muxeibs mqeibs els' i1 eid pos ow tp rcnt prot prioc wq cnsa mc o, 
    RH_ECBlk_EIBlk_Mux_P muxeibs els ->
    eibref_distinct semeibs muxeibs mqeibs ->
    join els' (sig eid (absmutexsem i1 o, nil)) els ->
    get muxeibs pos = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    RH_ECBlk_EIBlk_Mux_P (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) els'. 
Proof.
  introv Heibecb Hd Hjo Heib.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget Htp.
  casetac pos pos0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto.
  lets H00: Heibecb Hget Htp. clear Heibecb.
  simpljoin1.
  casetac eid0 eid Ht Hf.
  subst.
  unfold eibref_distinct in Hd.
  specialize (Hd eid).
  simpljoin1.
  unfold muxref_distinct in H2.
  lets H00: H2 Heib Hget.
  apply Hneq in H00. tryfalse.
  exists x x0 x1.
  assert (join (sig eid (absmutexsem i1 o, nil)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Fixpoint Get_structe (l: (list (addrval * type * (list val))))(a: addrval)(id: ident) :  (option val ) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  =>match t with 
                                                    | Tstruct sid decls =>  match id_nth id decls  with
                                                                                               | None => None
                                                                                               | Some n => nth_val n vl
                                                                                                end
                                                    | _ => None
                                                    end
                                   | false => Get_structe l' a id
                                   end  
end.

Lemma evref_same_type_muxrecv_preserve:
  forall eptr semeibs muxeibs mqeibs e o x n pro pi w c mc cn pos, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, o, x, n, pro, pi, w, c, mc) -> 
    evref_same_type eptr semeibs (MibMod.set muxeibs pos (e, o, x, cn, pro, pi, w, c, mc)) mqeibs. 
Proof.
  introv Hest Hget.
  unfold evref_same_type in *.
  destructs Hest.
  splits.
  -
    introv Hm.
    lets H00: H Hm. destructs H00. splits; auto.
    introv Hs. apply H2.
    unfold muxeib_ref in Hs. unfold muxeib_ref.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H4; eauto.
    do 8 eexists. eauto.
  -
    introv Hs.
    unfold muxeib_ref in *.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    apply H0.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H2; eauto. apply H0.
    do 8 eexists. eauto.
  -  
    introv Hq.
    lets H00: H1 Hq. destructs H00. splits; auto.
    introv Hs. apply H3.
    unfold muxeib_ref in Hs. unfold muxeib_ref.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H4; eauto.
    do 8 eexists. eauto.
Qed.

Lemma muxref_distinct_muxrecurv_preserve: 
  forall muxeibs eptr pos e o x n cn pro pi w c mc, 
    muxref_distinct muxeibs eptr -> 
    get muxeibs pos = Some (e, o, x, n, pro, pi, w, c, mc) ->
    muxref_distinct (MibMod.set muxeibs pos (e, o, x, cn, pro, pi, w, c, mc)) eptr. 
Proof.
  introv Hsr Hge.
  unfold muxref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq Hneq.
  casetac pos pos2 Heq1 Hneq1.
  subst. auto. subst.
  rewrite set_a_get_a in Hget1; eauto. inverts Hget1.
  rewrite set_a_get_a' in Hget2; eauto.
  casetac pos pos2 Heq1 Hneq1.
  subst. 
  rewrite set_a_get_a in Hget2; eauto. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma eibref_distinct_mux_setrecurv_preserve: 
  forall pos semeibs muxeibs mqeibs e o x n pro pi w c mc cn , 
eibref_distinct semeibs muxeibs mqeibs->
get muxeibs pos = Some (e, o, x, n, pro, pi, w, c, mc) ->
eibref_distinct semeibs (MibMod.set muxeibs pos (e, o, x, cn, pro, pi, w, c, mc)) mqeibs.
Proof.
  introv Hed Hget.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  mytac. splits; auto.
  eapply evref_same_type_muxrecv_preserve; eauto.
  eapply muxref_distinct_muxrecurv_preserve; eauto.
Qed.

Lemma evref_same_type_muxow_preserve:
  forall eptr semeibs muxeibs mqeibs ei o x n pro pi w c mc pos pip wl o' els eid, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (ei, o, x, n, pro, pi, w, c, mc) -> 
    ei = Valid_Addr eid ->
    EcbMod.get els eid = Some (absmutexsem pip o', wl) ->
    evref_same_type eptr semeibs (MibMod.set muxeibs pos (ei, o', x, n, pro, pi, w, c, mc)) mqeibs. 
Proof.
  introv Hest Hget Hei Hg.
  unfold evref_same_type in *.
  destructs Hest.
  splits.
  -
    introv Hm.
    lets H00: H Hm. destructs H00. splits; auto.
    introv Hs. apply H2.
    unfold muxeib_ref in Hs. unfold muxeib_ref.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H4; eauto.
    do 8 eexists. eauto.
  -
    introv Hs.
    unfold muxeib_ref in *.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    apply H0.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H2; eauto. apply H0.
    do 8 eexists. eauto.
  -  
    introv Hq.
    lets H00: H1 Hq. destructs H00. splits; auto.
    introv Hs. apply H3.
    unfold muxeib_ref in Hs. unfold muxeib_ref.
    simpljoin1.
    casetac pos x0 Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    do 8 eexists. eauto.
    rewrite set_a_get_a' in H4; eauto.
    do 8 eexists. eauto.
Qed.

Lemma muxref_distinct_muxow_preserve: 
  forall muxeibs eptr pos ei o x n pro pi w c mc pip o' wl els eid, 
    muxref_distinct muxeibs eptr -> 
    get muxeibs pos = Some (ei, o, x, n, pro, pi, w, c, mc) ->
    ei = Valid_Addr eid ->
    EcbMod.get els eid = Some (absmutexsem pip o', wl) ->
    muxref_distinct (MibMod.set muxeibs pos (ei, o', x, n, pro, pi, w, c, mc)) eptr. 
Proof.
  introv Hsr Hge Hei Hg.
  unfold muxref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq Hneq.
  casetac pos pos2 Heq1 Hneq1.
  subst. auto. subst.
  rewrite set_a_get_a in Hget1; eauto. inverts Hget1.
  rewrite set_a_get_a' in Hget2; eauto.
  casetac pos pos2 Heq1 Hneq1.
  subst. 
  rewrite set_a_get_a in Hget2; eauto. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma eibref_distinct_mux_setowner_preserve:
  forall pos semeibs muxeibs mqeibs ei ow o x n pro pi w c mc els wl eid pip, 
eibref_distinct semeibs muxeibs mqeibs->
get muxeibs pos = Some (ei, ow, x, n, pro, pi, w, c, mc) ->
ei = Valid_Addr eid ->
EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
eibref_distinct semeibs (MibMod.set muxeibs pos (ei, o, x, n, pro, pi, w, c, mc)) mqeibs.
Proof.
  introv Hed Hget Hei Hg.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  mytac. splits; auto.
  eapply evref_same_type_muxow_preserve; eauto.
  eapply muxref_distinct_muxow_preserve; eauto.
Qed.

Lemma SEM_ECB_P_setrecurv_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt rcnt' prot prioc wq cnsa mc, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (e, ow, tp, rcnt', prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hptr.
  lets H00: Hsep Hptr. clear Hsep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    repeat eexists; eauto.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma SEM_ECB_P_setow_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ei ow tp rcnt o prot prioc wq cnsa mc pip wl els eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (ei, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    ei = Valid_Addr eid ->
    EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (ei, o, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hsep Hget Hei Hg.
  unfold SEM_ECB_P in *.
  introv Hptr.
  lets H00: Hsep Hptr. clear Hsep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    repeat eexists; eauto.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma MUX_ECB_P_setrecurv_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt rcnt' prot prioc wq cnsa mc, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (e, ow, tp, rcnt', prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hptr.
  lets H00: Hmep Hptr. clear Hmep.
  destruct H00.
  -
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    repeat eexists; eauto.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma MUX_ECB_P_setow_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ei ow tp rcnt prot prioc wq cnsa mc pip o wl els eid, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (ei, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    ei = Valid_Addr eid ->
    EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (ei, o, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hmep Hget Hei Hg.
  unfold MUX_ECB_P in *.
  introv Hptr.
  lets H00: Hmep Hptr. clear Hmep.
  destruct H00.
  -
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    repeat eexists; eauto.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma Q_ECB_P_setrecurv_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt rcnt' prot prioc wq cnsa mc, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (e, ow, tp, rcnt', prot, prioc, wq, cnsa, mc)) mqeibs.  
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hptr.
  lets H00: Hqep Hptr. clear Hqep.
  destruct H00 as (Hor & Hdel).
  split.
  - (* part 1 *)
    destruct Hor.
    + 
      left.
      simpljoin1.
      splits; auto.
      introv Href. apply H1.
      unfold eib_ref in *.
      destruct Href; auto.
      destruct H3; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      repeat eexists; eauto. 
      rewrite set_a_get_a' in H3; eauto.
      repeat eexists; eauto.
    +
      destruct H.
      *
        right; left.
        simpljoin1.
        splits; auto.
        introv Href.
        apply H0.
        unfold eib_ref in Href. unfold eib_ref.
        destruct Href; auto.
        destruct H2; auto.
        right. left.
        unfold muxeib_ref in *.
        simpljoin1.
        casetac pos x Heq Hneq.
        subst. rewrite set_a_get_a in H2. inverts H2.
        repeat eexists; eauto.
        rewrite set_a_get_a' in H2; eauto.
        repeat eexists; eauto.
      *    
        simpljoin1.
        right. right.
        splits; auto.
  - (* part 2 *)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
    introv Href.
    apply H1.
    unfold eib_ref in Href. unfold eib_ref.
     destruct Href; auto.
      destruct H2; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
Qed.

Lemma Q_ECB_P_setow_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ei ow tp rcnt prot prioc wq cnsa mc els eid o pip wl, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (ei, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    ei = Valid_Addr eid ->
    EcbMod.get els eid = Some (absmutexsem pip o, wl) ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (ei, o, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.  
Proof.
  introv Hqep Hget Hei Hg.
  unfold Q_ECB_P in *.
  introv Hptr.
  lets H00: Hqep Hptr. clear Hqep.
  destruct H00 as (Hor & Hdel).
  split.
  - (* part 1 *)
    destruct Hor.
    + 
      left.
      simpljoin1.
      splits; auto.
      introv Href. apply H1.
      unfold eib_ref in *.
      destruct Href; auto.
      destruct H3; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      repeat eexists; eauto. 
      rewrite set_a_get_a' in H3; eauto.
      repeat eexists; eauto.
    +
      destruct H.
      *
        right; left.
        simpljoin1.
        splits; auto.
        introv Href.
        apply H0.
        unfold eib_ref in Href. unfold eib_ref.
        destruct Href; auto.
        destruct H2; auto.
        right. left.
        unfold muxeib_ref in *.
        simpljoin1.
        casetac pos x Heq Hneq.
        subst. rewrite set_a_get_a in H2. inverts H2.
        repeat eexists; eauto.
        rewrite set_a_get_a' in H2; eauto.
        repeat eexists; eauto.
      *    
        simpljoin1.
        right. right.
        splits; auto.
  - (* part 2 *)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
    introv Href.
    apply H1.
    unfold eib_ref in Href. unfold eib_ref.
     destruct Href; auto.
      destruct H2; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
Qed.

Lemma evdel_nodup_normal_muxptr_preserve: 
  forall locmp ptrmp tid sid, 
    evdel_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    evdel_nodup locmp (set ptrmp tid (Vptr sid, Vnull, Vnull)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold evdel_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.    

Lemma evcre_nodup_normal_muxptr_preserve: 
  forall locmp ptrmp tid sid, 
    evcre_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    evcre_nodup locmp (set ptrmp tid (Vptr sid, Vnull, Vnull)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold evcre_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. destruct Hgetl1; tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. destruct Hgetl2; tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.    

Lemma sem_ecb_p_muxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    SEM_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep Hgetl Hgetp Hsem.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.   

Lemma mux_ecb_p_nuxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    MUX_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep Hgetl Hgetp Hsem.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    right. right.
    splits; auto.
    left. unfold is_evt. right. left; auto.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.   

Lemma mq_ecb_p_muxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    Q_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hqep Hgetl Hgetp Hsem.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    auto. 
    introv Hdel'.
    apply Hdel in Hdel'.
    simpljoin.
    splits; auto.
    introv Hex.
    apply H0.
    simpljoin1.
    casetac x tid Ht' Hf'.
    subst.
    rewrite Hgetl in H2. destruct H2; tryfalse. 
    unfold evptr_of_tsk in H3. 
    rewrite set_a_get_a' in H3; eauto.
Qed.

Lemma Get_struct_muxattr:
forall v'35 v'36 x qid n l e qdata_vl,
 Get_struct
       (v'35 ++
        (x, pthread_mutexattr_t, update_nth_val n l e)
        :: v'36) qid = Some (qid, OS_Q_DATA, qdata_vl) ->
Get_struct (v'35 ++ (x, pthread_mutexattr_t, l) :: v'36)
  qid = Some (qid, OS_Q_DATA, qdata_vl).
Proof.
  inductions v'35.
  intros.
  simpl in *. 
  destruct (beq_addrval x qid) eqn:eq1.
  tryfalse. auto.
  intros.
  change ((a :: v'35) ++
       (x, pthread_mutexattr_t, update_nth_val n l e)
       :: v'36) with (a :: (v'35 ++
       (x, pthread_mutexattr_t, update_nth_val n l e)
       :: v'36)) in H.
  change ((a :: v'35) ++ (x, pthread_mutexattr_t, l) :: v'36) with
  (a :: (v'35 ++ (x, pthread_mutexattr_t, l) :: v'36)).
  unfold Get_struct in H; fold Get_struct in H.
  unfold Get_struct; fold Get_struct.
  destruct a. destruct p.
  destruct (beq_addrval a qid) eqn: eq1. auto.
  eapply IHv'35 in H; eauto.
Qed.

Lemma R_Q_Data_P_muxattr:
forall v'35 v'36 v'25 l e n x,
R_Q_Data_P
       (v'35 ++ (x, pthread_mutexattr_t, l) :: v'36) v'25 ->
R_Q_Data_P
  (v'35 ++(x, pthread_mutexattr_t, update_nth_val n l e) :: v'36) v'25.
Proof.
  intros.
  unfold R_Q_Data_P in *.
  inductions v'35.
  change ((nil ++ (x, pthread_mutexattr_t, update_nth_val n l e)
  :: v'36)) with (((x, pthread_mutexattr_t, update_nth_val n l e):: v'36)).
  change (nil ++ (x, pthread_mutexattr_t, l) :: v'36) with 
  ((x, pthread_mutexattr_t, l) :: v'36) in H.

  unfold Get_struct ; fold Get_struct.
  intros.
  destruct (beq_addrval x qid) eqn:eq1. tryfalse.
  specialize (H qid qdata_vl).
  unfold Get_struct in H; fold Get_struct in H.
  rewrite eq1 in H.
  eapply H in H0; eauto.
  intros.
  specialize (H qid qdata_vl).
  destruct a. destruct p.
  assert(Get_struct
      (((a, t, l0) :: v'35) ++
       (x, pthread_mutexattr_t, l) :: v'36) qid =
    Some (qid, OS_Q_DATA, qdata_vl)).
  change (((a, t, l0) :: v'35) ++
        (x, pthread_mutexattr_t, update_nth_val n l e)
        :: v'36) with ((a, t, l0) :: (v'35 ++
        (x, pthread_mutexattr_t, update_nth_val n l e)
        :: v'36)) in H0.
  change (((a, t, l0) :: v'35) ++
        (x, pthread_mutexattr_t, l) :: v'36) with ((a, t, l0) :: (v'35 ++
        (x, pthread_mutexattr_t, l) :: v'36)) in *.
  unfold Get_struct in H0, H; fold Get_struct in H0, H.
  unfold Get_struct; fold Get_struct.
   destruct (beq_addrval a qid) eqn:eq1.  auto.
  eapply Get_struct_muxattr; eauto.
  eapply H; eauto.
Qed.


Lemma RH_SEM_EINFO_ECB_P_muxpost_preserve: 
  forall ecbls sid embls pip t pt , 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    RH_SEM_EINFO_ECB_P ecbls embls -> 
    RH_SEM_EINFO_ECB_P (set ecbls sid (absmutexsem pip None, nil)) embls.  
Proof.
  introv How Hrh.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  apply Hrh in Hget.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.  

Lemma ASemEIBs_set_none_preserve: 
  forall s ecbls sid infol scapl embls vhold t pt pip P, 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    s |= ASemEIBs infol scapl embls ecbls vhold ** P -> 
    s |= ASemEIBs infol scapl embls (set ecbls sid (absmutexsem pip None, nil)) vhold ** P. 
Proof.
  introv How Haei.
  sep pauto.
  unfold ASemEIBs in *.
  sep pauto.
(*   sep split in Haei.
  sep split; auto. *)
  eapply RH_SEM_EINFO_ECB_P_muxpost_preserve; eauto.
Qed. 

Lemma RH_SEM_EINFO_ECB_P_muxpost_ow_preserve: 
  forall ecbls sid embls pip t pt wl t' pt' wl'  , 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    RH_SEM_EINFO_ECB_P ecbls embls -> 
    RH_SEM_EINFO_ECB_P (set ecbls sid (absmutexsem pip (Some (t', pt')), wl')) embls.  
Proof.
  introv How Hrh.
  unfold RH_SEM_EINFO_ECB_P in *.
  introv Hget.
  apply Hrh in Hget.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.  

Lemma ASemEIBs_set_ow_preserve: 
  forall s ecbls sid infol scapl embls vhold t pt pip wl t' pt' wl' P, 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    s |= ASemEIBs infol scapl embls ecbls vhold ** P -> 
    s |= ASemEIBs infol scapl embls (set ecbls sid (absmutexsem pip (Some (t', pt')), wl')) vhold ** P. 
Proof.
  introv How Haei.
  sep pauto.
  unfold ASemEIBs in *.
  sep pauto.
(*   sep split in Haei.
  sep split; auto. *)
  eapply RH_SEM_EINFO_ECB_P_muxpost_ow_preserve; eauto.
Qed. 

Lemma RH_ECBlk_EIBlk_Mux_P_muxpost_preserve: 
  forall ecbls sid embls pip t pt, 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    RH_ECBlk_EIBlk_Mux_P embls ecbls -> 
    RH_ECBlk_EIBlk_Mux_P embls (set ecbls sid (absmutexsem pip None, nil)).  
Proof.
  introv How Hrh.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget Heq.
  eapply Hrh in Hget; eauto.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  do 3 eexists.
  rewrite set_a_get_a; eauto.
  rewrite set_a_get_a'; eauto.
Qed.   

Lemma AMuxEIBs_set_none_preserve: 
  forall s ecbls sid infol mcapl embls vhold t pt pip  P,
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    s |= AMuxEIBs infol mcapl embls ecbls vhold ** P -> 
    s |= AMuxEIBs infol mcapl embls (set ecbls sid (absmutexsem pip None, nil)) vhold ** P. 
Proof.
  introv How Haei.
  sep pauto.
  unfold AMuxEIBs in *.
  sep pauto.
  (* sep split in Haei.
  sep split; auto. *)
  eapply RH_ECBlk_EIBlk_Mux_P_muxpost_preserve; eauto.
Qed. 

Lemma RH_ECBlk_EIBlk_Mux_P_muxpost_ow_preserve: 
  forall ecbls sid embls pip t pt wl t' pt' wl', 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    RH_ECBlk_EIBlk_Mux_P embls ecbls -> 
    RH_ECBlk_EIBlk_Mux_P embls (set ecbls sid (absmutexsem pip (Some (t', pt')), wl')).  
Proof.
  introv How Hrh.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  introv Hget Heq.
  eapply Hrh in Hget; eauto.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  do 3 eexists.
  rewrite set_a_get_a; eauto.
  rewrite set_a_get_a'; eauto.
Qed.   

Lemma AMuxEIBs_set_ow_preserve: 
  forall s ecbls sid infol mcapl embls vhold t pt pip wl t' pt' wl' P,
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    s |= AMuxEIBs infol mcapl embls ecbls vhold ** P -> 
    s |= AMuxEIBs infol mcapl embls (set ecbls sid (absmutexsem pip (Some (t', pt')), wl')) vhold ** P. 
Proof.
  introv How Haei.
  sep pauto.
  unfold AMuxEIBs in *.
  sep pauto.
 (* sep split in Haei.
  sep split; auto. *)
  eapply RH_ECBlk_EIBlk_Mux_P_muxpost_ow_preserve; eauto.
Qed. 

Lemma RH_EIBlk_ECBlk_Q_P_muxpost_preserve: 
  forall ecbls sid embls pip t pt , 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    RH_EIBlk_ECBlk_Q_P  ecbls embls -> 
    RH_EIBlk_ECBlk_Q_P (set ecbls sid (absmutexsem pip None, nil)) embls.  
Proof.
  introv How Hrh.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  eapply Hrh in Hget; eauto.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.

Lemma AMqEIBs_set_none_preserve: 
  forall s ecbls sid infol qcapl embls vhold t pt pip P, 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , nil) -> 
    s |= AMqEIBs infol qcapl embls ecbls vhold ** P -> 
    s |= AMqEIBs infol qcapl embls (set ecbls sid (absmutexsem pip None, nil)) vhold ** P. 
Proof.
  introv How Haei.
  unfold AMqEIBs in *.
  sep pauto.
  (* sep split in Haei.
  sep split; auto. *)
  eapply RH_EIBlk_ECBlk_Q_P_muxpost_preserve; eauto.
Qed. 

Lemma RH_EIBlk_ECBlk_Q_P_muxpost_ow_preserve: 
  forall ecbls sid embls pip t pt wl t' pt' wl' , 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    RH_EIBlk_ECBlk_Q_P  ecbls embls -> 
    RH_EIBlk_ECBlk_Q_P (set ecbls sid (absmutexsem pip (Some(t', pt')), wl')) embls.  
Proof.
  introv How Hrh.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  eapply Hrh in Hget; eauto.
  assert (eid = sid \/ eid <> sid) by tauto.
  destruct H.
  subst.
  unfold get in How, Hget.
  unfold EcbMap in How, Hget.
  rewrite How in Hget.
  simpljoin1. tryfalse.
  rewrite set_a_get_a'; eauto.
Qed.

Lemma AMqEIBs_set_ow_preserve: 
  forall s ecbls sid infol qcapl embls vhold t pt pip t' pt' wl wl' P, 
    get ecbls sid = Some (absmutexsem pip (Some(t, pt)) , wl) -> 
    s |= AMqEIBs infol qcapl embls ecbls vhold ** P -> 
    s |= AMqEIBs infol qcapl embls (set ecbls sid (absmutexsem pip (Some(t', pt')), wl')) vhold ** P. 
Proof.
  introv How Haei.
  unfold AMqEIBs in *.
  sep pauto.
  (* sep split in Haei.
  sep split; auto. *)
  eapply RH_EIBlk_ECBlk_Q_P_muxpost_ow_preserve; eauto.
Qed. 

Lemma get_struct_or : forall ma a, Get_struct ma a = None \/ exists t, Get_struct ma a = Some t.
Proof.
  intros.
  assert ( exists t, Get_struct ma a = t) by eauto.
  destruct H.
  destruct x.
  right; eauto.
  left; eauto.
Qed.

Lemma get_heap_or : forall ma a, Get_heap ma a = None \/ exists t, Get_heap ma a = Some t.
Proof.
  intros.
  assert ( exists t, Get_heap ma a = t) by eauto.
  destruct H.
  destruct x.
  right; eauto.
  left; eauto.
Qed.

Lemma set_struct_update_nth_val: 
  forall vl1 x l vl2 v n sid decls id, 
  Get_struct (vl1 ++ (x, (Tstruct sid decls), l)  :: vl2) x = Some (x,  (Tstruct sid decls), l) ->
  Get_struct vl1 x = None ->
  id_nth id decls = Some n ->
  Set_struct' (vl1 ++ (x, (Tstruct sid decls), l) :: vl2) x id v =
    vl1 ++ (x, (Tstruct sid decls), update_nth_val n l v) :: vl2.
Proof.
  intros.
  inductions vl1.
  simpl. 
  rewrite beq_tid_true. rewrite H1; auto.
  unfold Get_struct in H, H0.
  destruct a. destruct p.
  fold Get_struct in H, H0.
  change (((a, t, l0) :: vl1) ++ (x, STRUCT sid ­{ decls }­, l) :: vl2) with 
    ((a, t, l0) :: (vl1 ++ (x, STRUCT sid ­{ decls }­, l) :: vl2)) in *.
  unfold Get_struct in *; fold Get_struct in *.
  destruct (os_inv.beq_addrval a x) eqn: eq1. inverts H.  tryfalse.
  unfold Set_struct'; fold Set_struct'.
  rewrite eq1.
  fold Get_struct in*.
  simpl.
  lets Hs: IHvl1 H H0 H1.
  instantiate (1:= v) in Hs.
  inverts Hs; auto.
Qed.

Lemma set_struct_update_nth_val': 
  forall vl1 x l vl2 v n sid decls id l', 
  Get_struct (vl1 ++ (x, (Tstruct sid decls), l)  :: vl2) x = Some (x,  (Tstruct sid decls), l) ->
  Get_struct vl1 x = None ->
  id_nth id decls = Some n ->
  l' = update_nth_val n l v ->
  Set_struct' (vl1 ++ (x, (Tstruct sid decls), l) :: vl2) x id v =
    vl1 ++ (x, (Tstruct sid decls), l') :: vl2.
Proof.
  intros. substs.
  eapply set_struct_update_nth_val; eauto.
Qed.

Lemma Get_struct_some_eq:
  forall evheap x a t l,
  Get_struct evheap x = Some (a, t, l) -> x = a.
Proof.
  intros.
  inductions evheap.
  simpl in H; tryfalse.
  unfold Get_struct in H.
  destruct a. destruct p. 
  destruct (beq_addrval a x) eqn: eq1.
  eapply TcbMod.option2val in H.
  inverts H; auto.
  fold Get_struct in H.
  apply IHevheap in H; eauto.
Qed.

Lemma Get_structe_eq:
  forall id decls n x l vl1 vl2 sid,
  Get_struct (vl1 ++ (x, (Tstruct sid decls), l)  :: vl2) x = Some (x,  (Tstruct sid decls), l) ->
  Get_struct vl1 x = None ->
  id_nth id decls = Some n ->
  Get_structe (vl1 ++ (x, Tstruct sid decls, l) :: vl2) x id = nth_val n l.
Proof.
  intros.
  inductions vl1.
  simpl.
  rewrite beq_tid_true. auto.
  unfold Get_struct in H, H0.
  rewrite H1; eauto.
  destruct a. destruct p.
  destruct (beq_addrval a x) eqn: eq1.
  unfold Get_struct in H, H0. rewrite eq1 in H0. 
  tryfalse.
  change (((a, t, l0) :: vl1) ++ (x, STRUCT sid ­{ decls }­, l) :: vl2) with
           ((a, t, l0) :: (vl1 ++ (x, STRUCT sid ­{ decls }­, l) :: vl2)) in *.
  unfold Get_struct in H, H0.
  rewrite eq1 in H.
  fold Get_struct in H.
  unfold Get_structe. rewrite eq1.
  fold Get_structe. rewrite eq1 in H0.
  fold Get_struct in H, H0.
  eapply IHvl1; eauto.
Qed.

Lemma Vneq:
  forall a b,
  Vint32 a <> Vint32 b -> a <> b.
Proof.
  intros.
  unfolds.
  intros. 
  subst a. tryfalse.
Qed.
