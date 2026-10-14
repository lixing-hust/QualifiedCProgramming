Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_inv.
Require Import sep_auto.
Require Import gjb_common.
Require Import seplog_trm_tacs.
Require Import ucos_common.
Require Import partition_common.
Require Import symbolic_lemmas.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
    Proof.
      intros.
      unfolds in H; destruct t1; destruct t2.
      apply andb_true_iff in H; destruct H.
      rewrite beq_pos_Pos_eqb_eq in H.
      apply Pos.eqb_eq in H.
      pose proof Int.eq_spec i i0.
      rewrite H0 in H1.
      substs; auto.
    Qed.

Lemma AEvStructHeap_SMSL_unfold: 
  forall s evstructs q vll P smsmpaxl,
    s |=  AEvStructHeap evstructs ** 
          LV smsmpaxl @ (MSMC_SMSMPAXL) ∗ |-> Vptr q ** P->
            Get_struct evstructs q = Some (q, MSMC_SMSMPAXL, vll) ->
    s |= EX evh1 evh2,
                 Astruct q MSMC_SMSMPAXL vll ** 
                [|struct_type_vallist_match MSMC_SMSMPAXL vll|] **
                [|R_MutexAttr_P MSMC_SMSMPAXL vll|] ** (* new add *)
                LV smsmpaxl @ (MSMC_SMSMPAXL) ∗ |-> Vptr q **
                [| evstructs =(evh1 ++ (q, MSMC_SMSMPAXL, vll) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 q = None|] **
                P.
Proof.
  introv Hsat Hget.
  inductions evstructs. tryfalse. 
  destruct a. destruct p.
  rename evstructs into evstructs'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a q) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evstructs'.
  sep normal in Hsat.
  change (nil ++ (q, MSMC_SMSMPAXL, vll) :: evstructs') with ((q, MSMC_SMSMPAXL, vll) :: evstructs').

  sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
  eapply IHevstructs in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x ++ (q, MSMC_SMSMPAXL, vll) :: x0)) with
 (((a, STRUCT i ­{ d }­, l) :: x ) ++ (q, MSMC_SMSMPAXL, vll) :: x0).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2.
  auto.
Qed.

Lemma AEvStructHeap_SESL_unfold: 
  forall s evstructs q vll P sesmpaxl,
    s |=  AEvStructHeap evstructs ** 
          LV sesmpaxl @ (MSMC_SESMPAXL) ∗ |-> Vptr q ** P->
            Get_struct evstructs q = Some (q, MSMC_SESMPAXL, vll) ->
    s |= EX evh1 evh2,
                 Astruct q MSMC_SESMPAXL vll ** 
                [|struct_type_vallist_match MSMC_SESMPAXL vll|] **
                [|R_MutexAttr_P MSMC_SESMPAXL vll|] ** (* new add *)
                LV sesmpaxl @ (MSMC_SESMPAXL) ∗ |-> Vptr q **
                [| evstructs =(evh1 ++ (q, MSMC_SESMPAXL, vll) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 q = None|] **
                P.
Proof.
  introv Hsat Hget.
  inductions evstructs. tryfalse. 
  destruct a. destruct p.
  rename evstructs into evstructs'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a q) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evstructs'.
  sep normal in Hsat.
  change (nil ++ (q, MSMC_SESMPAXL, vll) :: evstructs') with ((q, MSMC_SESMPAXL, vll) :: evstructs').

  sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
  eapply IHevstructs in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x ++ (q, MSMC_SESMPAXL, vll) :: x0)) with
 (((a, STRUCT i ­{ d }­, l) :: x ) ++ (q, MSMC_SESMPAXL, vll) :: x0).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2.
  auto.
Qed.

Lemma AEvStructHeap_XMCL_unfold': 
  forall s evstructs q vll P xmpaxl,
    s |=  AEvStructHeap evstructs ** 
          LV xmpaxl @ (XMC_XMPAXL) ∗ |-> Vptr q ** P->
            Get_struct evstructs q = Some (q, XMC_XMPAXL, vll) ->
    s |= EX evh1 evh2,
                 Astruct q XMC_XMPAXL vll ** 
                [|struct_type_vallist_match XMC_XMPAXL vll|] **
                [|R_MutexAttr_P XMC_XMPAXL vll|] ** (* new add *)
                LV xmpaxl @ (XMC_XMPAXL) ∗ |-> Vptr q **
                [| evstructs =(evh1 ++ (q, XMC_XMPAXL, vll) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 q = None|] **
                P.
Proof.
  introv Hsat Hget.
  inductions evstructs. tryfalse. 
  destruct a. destruct p.
  rename evstructs into evstructs'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.
  unfold Get_struct in Hget.

  destruct (os_inv.beq_addrval a q) eqn: eq1.
  eexists. instantiate (1:= nil).
  exists evstructs'.
  sep normal in Hsat.
  change (nil ++ (q, XMC_XMPAXL, vll) :: evstructs') with ((q, XMC_XMPAXL, vll) :: evstructs').

  sep pauto.
  eapply beq_tid_true_eq in eq1.
  inverts Hget.
  fold AEvStructHeap in Hsat.
  sep pauto.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep pauto.
  inverts Hget. 
  eapply beq_tid_true_eq in eq1. subst a.
  auto. 
  (* new add about R_MutexAttr_P *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  (* end of new add *)
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  inverts Hget. sep pauto.
  fold Get_struct in Hget.
  unfold AEvStructHeap in Hsat.
  fold AEvStructHeap in Hsat.
  sep normal in Hsat.
  sep lifts (4::5::nil)%nat in Hsat.
  eapply IHevstructs in Hsat; eauto.
  sep pauto.
  3:{
  change((a, STRUCT i ­{ d }­, l) :: ( x ++ (q, XMC_XMPAXL, vll) :: x0)) with
 (((a, STRUCT i ­{ d }­, l) :: x ) ++ (q, XMC_XMPAXL, vll) :: x0).
  eauto. }
  simpl AEvStructHeap at 1.
  sep pauto.
  unfold Get_struct; fold Get_struct.
  rewrite eq1, H2.
  auto.
Qed.

Lemma AEvStructHeap_SMSL_fold: 
  forall s evstructs q P,
    s |= EX vll evh1 evh2,
         Astruct q MSMC_SMSMPAXL vll ** 
         [|struct_type_vallist_match MSMC_SMSMPAXL vll|] ** 
         [|R_MutexAttr_P MSMC_SMSMPAXL vll|] **
         [| evstructs =(evh1 ++ (q, MSMC_SMSMPAXL, vll) :: evh2) |] **
         AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
         [|Get_struct evh1 q = None|] ** P ->
    s |= AEvStructHeap evstructs ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  sep pauto.
Qed.

Lemma AEvStructHeap_SESL_fold: 
  forall s evstructs q P,
    s |= EX vll evh1 evh2,
         Astruct q MSMC_SESMPAXL vll ** 
         [|struct_type_vallist_match MSMC_SESMPAXL vll|] ** 
         [|R_MutexAttr_P MSMC_SESMPAXL vll|] **
         [| evstructs =(evh1 ++ (q, MSMC_SESMPAXL, vll) :: evh2) |] **
         AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
         [|Get_struct evh1 q = None|] ** P ->
    s |= AEvStructHeap evstructs ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  sep pauto.
Qed.

Lemma AEvStructHeap_XMCL_fold: 
  forall s evstructs q P,
    s |= EX vll evh1 evh2,
         Astruct q XMC_XMPAXL vll ** 
         [|struct_type_vallist_match XMC_XMPAXL vll|] ** 
         [|R_MutexAttr_P XMC_XMPAXL vll|] **
         [| evstructs =(evh1 ++ (q, XMC_XMPAXL, vll) :: evh2) |] **
         AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
         [|Get_struct evh1 q = None|] ** P->
    s |= AEvStructHeap evstructs ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  sep pauto.
Qed.

Lemma AEvStructHeap_fold': 
  forall s evstructs q P,
    s |= EX vll evh1 evh2 sid decls,
         Astruct q (Tstruct sid decls) vll ** 
         [|struct_type_vallist_match (Tstruct sid decls) vll|] ** 
         [|R_MutexAttr_P (Tstruct sid decls) vll|] **
         [| evstructs =(evh1 ++ (q, (Tstruct sid decls), vll) :: evh2) |] **
         AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
         [|Get_struct evh1 q = None|] ** P ->
    s |= AEvStructHeap evstructs ** P.
Proof.
  intros.
  unfold AEvStructHeap.
  sep pauto.
  fold AEvStructHeap.
  apply AEvStructHeap_compose.
  sep pauto.
  unfold AEvStructHeap.
  fold AEvStructHeap.
  sep pauto.
Qed.

Lemma beq_pos_true : forall p, beq_pos p p = true.
Proof.
  inductions p.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  simpl; auto.
Qed.

Lemma beq_tid_true :
  forall tid, beq_tid tid tid = true.
Proof.
  intros.
  unfolds.
  destruct tid.
  rewrite beq_pos_true.
  rewrite Int.eq_true.
  auto.
Qed.


Lemma get_set_struct_smsl_vl: 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0) q = Some (q , MSMC_SMSMPAXL, vl) ->
    Get_struct v' q = None ->
    Get_struct (Set_struct (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0) q MSMC_SMSMPAXL vl') q = Some (q, MSMC_SMSMPAXL, vl').
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true.
  simpl.
  rewrite beq_tid_true; eauto.
  change ((a :: v') ++ (q, MSMC_SMSMPAXL, vl) :: v'0) with 
    (a :: (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in H0.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct, Get_struct in *.
  rewrite eq.
  fold Set_struct Get_struct in *.
  rewrite eq in *.
  lets Hs: IHv' H H0.
  eauto.
Qed.

Lemma get_set_struct_sesl_vl: 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0) q = Some (q , MSMC_SESMPAXL, vl) ->
    Get_struct v' q = None ->
    Get_struct (Set_struct (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0) q MSMC_SESMPAXL vl') q = Some (q, MSMC_SESMPAXL, vl').
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true.
  simpl.
  rewrite beq_tid_true; eauto.
  change ((a :: v') ++ (q, MSMC_SESMPAXL, vl) :: v'0) with 
    (a :: (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in H0.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct, Get_struct in *.
  rewrite eq.
  fold Set_struct Get_struct in *.
  rewrite eq in *.
  lets Hs: IHv' H H0.
  eauto.
Qed.

Lemma get_set_struct_xmcl_vl: 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, XMC_XMPAXL, vl) :: v'0) q = Some (q , XMC_XMPAXL, vl) ->
    Get_struct v' q = None ->
    Get_struct (Set_struct (v' ++ (q, XMC_XMPAXL, vl) :: v'0) q XMC_XMPAXL vl') q = Some (q, XMC_XMPAXL, vl').
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true.
  simpl.
  rewrite beq_tid_true; eauto.
  change ((a :: v') ++ (q, XMC_XMPAXL, vl) :: v'0) with 
    (a :: (v' ++ (q, XMC_XMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in H0.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct, Get_struct in *.
  rewrite eq.
  fold Set_struct Get_struct in *.
  rewrite eq in *.
  lets Hs: IHv' H H0.
  eauto.
Qed.

Lemma set_struct_update_vl: 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, XMC_XMPAXL, vl) :: v'0) q = Some (q , XMC_XMPAXL, vl) ->
    Get_struct v' q = None ->
    Set_struct (v' ++ (q, XMC_XMPAXL, vl) :: v'0) q XMC_XMPAXL vl' = v' ++ (q, XMC_XMPAXL, vl') :: v'0.
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true; eauto.
  unfold Get_struct in H, H0.
  destruct a. destruct p.
  fold Get_struct in H, H0.
  change  (((a, t, l) :: v') ++ (q, XMC_XMPAXL, vl) :: v'0) with 
    ((a, t, l) :: (v' ++ (q, XMC_XMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in *; fold Get_struct in *.
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct; fold Set_struct.
  rewrite eq.
  simpl.
  lets Hs: IHv' H H0.
  inverts Hs; eauto.
Qed.

Lemma set_struct_update_vl': 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0) q = Some (q , MSMC_SMSMPAXL, vl) ->
    Get_struct v' q = None ->
    Set_struct (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0) q MSMC_SMSMPAXL vl' = v' ++ (q, MSMC_SMSMPAXL, vl') :: v'0.
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true; eauto.
  unfold Get_struct in H, H0.
  destruct a. destruct p.
  fold Get_struct in H, H0.
  change  (((a, t, l) :: v') ++ (q, MSMC_SMSMPAXL, vl) :: v'0) with 
    ((a, t, l) :: (v' ++ (q, MSMC_SMSMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in *; fold Get_struct in *.
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct; fold Set_struct.
  rewrite eq.
  simpl.
  lets Hs: IHv' H H0.
  inverts Hs; eauto.
Qed.

Lemma get_struct_vl':
forall v' v'0 q t vl,
  Get_struct v' q = None ->
  Get_struct (v' ++ (q, t, vl) :: v'0) q = Some (q, t ,vl).
Proof.
  intros.
  inductions v'.
  simpl.
  rewrite beq_tid_true; eauto.
  unfold Get_struct in H.
  destruct a. destruct p.
  fold Get_struct in H.
  change (((a, t0, l) :: v') ++ (q, t, vl) :: v'0) with ((a, t0, l) :: (v' ++ (q, t, vl) :: v'0)) in *.
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Get_struct; fold Get_struct.
  rewrite eq.
  eapply IHv'; eauto.
Qed.

Lemma set_struct_update_ses_vl: 
  forall q vl vl' v' v'0,
    Get_struct (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0) q = Some (q , MSMC_SESMPAXL, vl) ->
    Get_struct v' q = None ->
    Set_struct (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0) q MSMC_SESMPAXL vl' = v' ++ (q, MSMC_SESMPAXL, vl') :: v'0.
Proof.
  intros.
  inductions v'.
  simpl. 
  rewrite beq_tid_true; eauto.
  unfold Get_struct in H, H0.
  destruct a. destruct p.
  fold Get_struct in H, H0.
  change  (((a, t, l) :: v') ++ (q, MSMC_SESMPAXL, vl) :: v'0) with 
    ((a, t, l) :: (v' ++ (q, MSMC_SESMPAXL, vl) :: v'0)) in *.
  unfold Get_struct in *; fold Get_struct in *.
  destruct (os_inv.beq_addrval a q) eqn:eq.
  tryfalse.
  unfold Set_struct; fold Set_struct.
  rewrite eq.
  simpl.
  lets Hs: IHv' H H0.
  inverts Hs; eauto.
Qed.

Lemma AEvStructHeap_unfold_gen: 
  forall evheap tp ident s l vl P,
    s |= AEvStructHeap evheap **
            LV ident @ tp ∗ |-> Vptr l ** P->
    Get_struct evheap l = Some (l, tp, vl) ->
    s |= EX evh1 evh2,
                 Astruct l tp vl ** 
                [|struct_type_vallist_match tp vl|] **
                [|R_MutexAttr_P tp vl|] **
                LV ident @ tp ∗ |-> Vptr l **
                [| evheap =(evh1 ++ (l, tp, vl) :: evh2) |] **
                AEvStructHeap evh1 ** AEvStructHeap evh2 ** 
                [|Get_struct evh1 l = None|] **
                P.
Proof.
induction evheap; introv Hsat Hget.
simpl in Hget; tryfalse.
destruct a as [[]].
simpl in Hget.
unfold AEvStructHeap in Hsat; fold AEvStructHeap in Hsat.
destruct t;
try solve [eapply astar_l_afalse_elim in Hsat; simpl in Hsat; simpljoin; tryfalse].
destruct (beq_addrval a l) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
inverts Hget.
exists (nil: list (addrval * type * list val)) evheap.
sep pauto.
sep_lifts_trms_in Hsat (AEvStructHeap, ident).
eapply IHevheap in Hsat; eauto.
sep destruct Hsat.
exists ((a, STRUCT i ­{ d }­, l0) :: x) x0.
simpl AEvStructHeap.
sep pauto.
simpl.
rewrite eq1.
auto.
Qed.

Lemma  Int_mul_eq: 
  forall m n,
    Int.unsigned m <= Int.max_signed ->
    Z.of_nat (n) <= Int.max_signed -> 
    $ Z.of_nat (Z.to_nat (Int.unsigned m) * n) = 
      Int.mul ($ Z.of_nat n) m.
Proof.
  intros.
  rewrite Nat2Z.inj_mul.
  rewrite Int.mul_commut.
  rewrite Z2Nat.id.
  rewrite Int.mul_signed.
  rewrite Int.signed_repr; eauto.
  rewrite Int.signed_eq_unsigned; eauto.
  split; auto.
  eapply Z.le_trans; try apply Zle_0_nat; eauto.
  conv_max_unsigned'. auto with zarith.
  apply Int.unsigned_range_2.
Qed.

Lemma Axmpaxinfo_unfold_any_idx_frm:
forall xmpaxvl s P idx,
        Z.of_nat idx < 32 ->
        s |= Axmpaxinfo xmpaxvl ** P ->
        s |= PV (xmpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> (nth_val' idx xmpaxvl) **
                Aarray_rm (xmpax_block,Int.zero) (Z.to_nat 32) Tint32 xmpaxvl idx **
               [|array_type_vallist_match Tint32 xmpaxvl|] ** P.
Proof.
unfold Axmpaxinfo.
intros.
sep normal in H0.
lets Hlen: Aarray_vl_len_eq H0.
unfold nat_of_Z in *.
sep pauto.
unfold Aarray in *.
unfold xmpax_addr in *.
eapply array_asrt_eq in H0; eauto.
unfold nat_of_Z in *.
simpl typelen in *.
change (Z.of_nat 4) with 4 in *.
rewrite Int.add_zero_l in *.
sep pauto.
unfold nat_of_Z in *.
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite Hlen.
auto with zarith.
Qed.

Lemma Axmpaxinfo_fold_frm:
forall xmpaxvl s P,
        (length xmpaxvl = 32)%nat ->
        s |= EX idx v,
                PV (xmpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> v **
                Aarray_rm (xmpax_block,Int.zero) (Z.to_nat 32) Tint32 xmpaxvl idx **
                [| v = (nth_val' idx xmpaxvl) |] **
                [| Z.of_nat idx < 32 |] **
                [|array_type_vallist_match Tint32 xmpaxvl|] ** P ->
        s |= Axmpaxinfo xmpaxvl ** P.
Proof.
intros.
unfold Axmpaxinfo.
sep destruct H0.
sep split in H0.
simpljoin.
sep normal.
sep pauto.
unfold nat_of_Z in *.
unfold Aarray in *.
unfold xmpax_addr in *.
eapply array_asrt_eq; eauto.
3:{ rewrite Int.add_zero_l.
       simpl typelen.
       change (Z.of_nat 4) with 4.
       sep pauto. }
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite H.
auto with zarith.
Qed.

Lemma Ases_mpaxinfo_unfold_any_idx_frm:
forall vl s P idx,
        Z.of_nat idx < 16 ->
        s |= Ases_mpaxinfo vl ** P ->
        s |= PV (ses_mpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> (nth_val' idx vl) **
                Aarray_rm (ses_mpax_block,Int.zero) (Z.to_nat 16) Tint32 vl idx **
               [|array_type_vallist_match Tint32 vl|] ** P.
Proof.
unfold Ases_mpaxinfo.
intros.
sep normal in H0.
lets Hlen: Aarray_vl_len_eq H0.
unfold nat_of_Z in *.
sep pauto.
unfold Aarray in *.
unfold ses_mpax_addr in *.
eapply array_asrt_eq in H0; eauto.
unfold nat_of_Z in *.
simpl typelen in *.
change (Z.of_nat 4) with 4 in *.
rewrite Int.add_zero_l in *.
sep pauto.
unfold nat_of_Z in *.
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite Hlen.
auto with zarith.
Qed.

Lemma Ases_mpaxinfo_fold_frm:
forall vl s P,
        (length vl = 16)%nat ->
        s |= EX idx v,
                PV (ses_mpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> v **
                Aarray_rm (ses_mpax_block,Int.zero) (Z.to_nat 16) Tint32 vl idx **
                [| v = (nth_val' idx vl) |] **
                [| Z.of_nat idx < 16 |] **
                [|array_type_vallist_match Tint32 vl|] ** P ->
        s |= Ases_mpaxinfo vl ** P.
Proof.
intros.
unfold Ases_mpaxinfo.
sep destruct H0.
sep split in H0.
simpljoin.
sep normal.
sep pauto.
unfold nat_of_Z in *.
unfold Aarray in *.
eapply array_asrt_eq; eauto.
3:{ rewrite Int.add_zero_l.
       simpl typelen.
       change (Z.of_nat 4) with 4.
       sep pauto. }
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite H.
auto with zarith.
Qed.

Lemma Asms_mpaxinfo_unfold_any_idx_frm:
forall vl s P idx,
        Z.of_nat idx < 16 ->
        s |= Asms_mpaxinfo vl ** P ->
        s |= PV (sms_mpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> (nth_val' idx vl) **
                Aarray_rm (sms_mpax_block,Int.zero) (Z.to_nat 16) Tint32 vl idx **
               [|array_type_vallist_match Tint32 vl|] ** P.
Proof.
unfold Asms_mpaxinfo.
intros.
sep normal in H0.
lets Hlen: Aarray_vl_len_eq H0.
unfold nat_of_Z in *.
sep pauto.
unfold Aarray in *.
unfold sms_mpax_addr in *.
eapply array_asrt_eq in H0; eauto.
unfold nat_of_Z in *.
simpl typelen in *.
change (Z.of_nat 4) with 4 in *.
rewrite Int.add_zero_l in *.
sep pauto.
unfold nat_of_Z in *.
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite Hlen.
auto with zarith.
Qed.

Lemma Asms_mpaxinfo_fold_frm:
forall vl s P,
        (length vl = 16)%nat ->
        s |= EX idx v,
                PV (sms_mpax_block, (Int.mul (Int.repr 4) (Int.repr  (Z.of_nat idx)))) @ Tint32 |-> v **
                Aarray_rm (sms_mpax_block,Int.zero) (Z.to_nat 16) Tint32 vl idx **
                [| v = (nth_val' idx vl) |] **
                [| Z.of_nat idx < 16 |] **
                [|array_type_vallist_match Tint32 vl|] ** P ->
        s |= Asms_mpaxinfo vl ** P.
Proof.
intros.
unfold Asms_mpaxinfo.
sep destruct H0.
sep split in H0.
simpljoin.
sep normal.
sep pauto.
unfold nat_of_Z in *.
unfold Aarray in *.
eapply array_asrt_eq; eauto.
3:{ rewrite Int.add_zero_l.
       simpl typelen.
       change (Z.of_nat 4) with 4.
       sep pauto. }
auto with zarith.
eapply nth_val_imp_nth_val'_2.
rewrite H.
auto with zarith.
Qed.

Lemma Get_struct_Set_vl: 
  forall vll1 vll2 q vl vl' tp,
    Get_struct (vll1 ++ (q, tp, vl) :: vll2) q = Some (q , tp, vl) ->
    Get_struct vll1 q = None ->
    Get_struct (Set_struct (vll1 ++ (q, tp, vl) :: vll2) q tp vl') q = Some (q, tp, vl').
Proof.
  induction vll1; simpl.
  intros.
  rewrite beq_tid_true.
  destruct (type_eq tp tp) eqn: eq1.
  simpl;  rewrite beq_tid_true; auto.
  eapply type_eq_false_neq in eq1; tryfalse.
  intros.
  destruct a as [[]].
  destruct (beq_addrval a q) eqn: eq1.
  tryfalse.
  simpl.
  rewrite eq1.
  eapply IHvll1; eauto.
Qed.

Lemma set_struct_update_vl_gen:
  forall  vll1 vll2 q vl vl' tp,
    Get_struct (vll1 ++ (q, tp, vl) :: vll2) q = Some (q , tp, vl) ->
    Get_struct vll1 q = None ->
    Set_struct (vll1 ++ (q, tp, vl) :: vll2) q tp vl' = vll1 ++ (q, tp, vl') :: vll2.
Proof.
  induction vll1; simpl.
  intros.
  rewrite beq_tid_true.
  destruct (type_eq tp tp) eqn: eq1; auto.
  eapply type_eq_false_neq in eq1; tryfalse.
  intros.
  destruct a as [[]].
  destruct (beq_addrval a q) eqn: eq1.
  tryfalse.
  eapply IHvll1 in H; eauto.
  erewrite H; auto.
Qed.

Lemma get_set_struct_notequal:
forall q1 q2 t evstructs x',
  q1 <> q2 ->
  Get_struct (Set_struct evstructs q1 t x') q2 = Get_struct evstructs q2.
Proof.
  intros.
  induction evstructs.
  simpl; auto.
  unfold Set_struct.
  destruct a. destruct p.
  destruct (beq_addrval a q1) eqn:eq.
  destruct (type_eq t0 t) eqn:eq1.
  unfold Get_struct.
  destruct (beq_addrval a q2) eqn:eq2.
  eapply beq_tid_true_eq in eq,eq2.
  tryfalse.
  fold Get_struct; auto.
  fold Set_struct.
  unfold Get_struct.
  destruct (beq_addrval a q2) eqn:eq2; auto.
  fold Set_struct.
  unfold Get_struct.
  destruct (beq_addrval a q2) eqn:eq2; auto.
Qed.

Lemma set_struct_comm:
forall evstructs l1 t1 vl1 l2 t2 vl2,
  l1 <> l2 ->
  Set_struct (Set_struct evstructs l1 t1 vl1) l2 t2 vl2 = Set_struct (Set_struct evstructs l2 t2 vl2) l1 t1 vl1.
Proof.
induction evstructs; introv Hneq; simpl; auto.
destruct a as [[]].
destruct (beq_addrval a l1) eqn:eq1;
destruct (beq_addrval a l2) eqn:eq2;
try eapply beq_tid_true_eq in eq1;
try eapply beq_tid_true_eq in eq2;
subst; tryfalse.
destruct (type_eq t t1) eqn: eq3; simpl;
try rewrite beq_tid_true; try rewrite eq2; try rewrite eq3; auto.
rewrite IHevstructs; auto.
destruct (type_eq t t2) eqn: eq3; simpl;
try rewrite beq_tid_true; try rewrite eq1; try rewrite eq3; auto.
rewrite IHevstructs; auto.
simpl; rewrite eq1; rewrite eq2.
rewrite IHevstructs; auto.
Qed.

Lemma set_struct_eq:
forall evstructs l t vl1 vl2,
  Set_struct (Set_struct evstructs l t vl1) l t vl2 = Set_struct evstructs l t vl2.
Proof.
induction evstructs; intros; simpl; auto.
destruct a as [[]].
destruct (beq_addrval a l) eqn:eq1;
try eapply beq_tid_true_eq in eq1;
subst; tryfalse.
destruct (type_eq t0 t) eqn: eq2; simpl;
try rewrite beq_tid_true; try rewrite eq1; try rewrite eq2; auto.
rewrite IHevstructs; auto.
simpl; rewrite eq1.
rewrite IHevstructs; auto.
Qed.

