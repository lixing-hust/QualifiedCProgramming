Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.
Require Import os_inv.

Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import math_auto.
Require Import OSTimeTickPure.

Open Scope list_scope.
Open Scope code_scope.

Fixpoint Get_heap (l: (list (addrval * type * val)))(a: addrval) :  (option (addrval * type * val )) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_heap l' a 
                                   end  
end.

Fixpoint Set_sval (l: (list (addrval * type *  val )))(a: addrval) (b: val)
     :  (list (addrval * type *  val)):=
  match l with 
  | nil => nil  
  | (ad, t, v ) :: l' => match (beq_tid ad a) with
                                   | true  => ((a, t, b) :: l')
                                   | false => ((ad, t, v ) :: (Set_sval l' a b))
                                   end
end.

Lemma option2val:
  forall T (x y: T),
    Some x = Some y -> x = y.
Proof.
  intros T x y.
  intros F1.
  inversion F1.
  trivial.
Qed.

Lemma AEvAtomHeap_unfold: 
  forall s evhpe x v P ident,
    s |= AEvAtomHeap evhpe **
            LV ident @ (long) ∗ |-> Vptr x ** P->
            Get_heap evhpe x = Some (x, Tint32, v) ->
    s |= EX evh1 evh2,
                PV x @ Tint32 |-> v **
                LV ident @ (long) ∗ |-> Vptr x  **
                [| evhpe =(evh1 ++ (x, Tint32, v) :: evh2) |] **
                AEvAtomHeap evh1 ** AEvAtomHeap evh2 ** 
                [|Get_heap evh1 x = None|] **
                [|rule_type_val_match Tint32 v = true|] ** (* new add *)
                P.
Proof.
  introv Hsat Hget.
(*   sep pauto. *)
  inductions evhpe. tryfalse. 
  destruct a. destruct p.
  rename evhpe into evhpe'.
  destruct t;
  try eapply astar_l_afalse_elim in Hsat;  tryfalse.

  unfold Get_heap in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eapply option2val in Hget;
  tryfalse.
  fold Get_heap in Hget.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevhpe in Hsat; eauto.
  sep pauto.
  3:{
  change ((a, Void, v0) :: (x0 ++ (x, long, v) :: x1)) with 
    (((a, Void, v0) :: x0) ++ ((x, long, v) :: x1)).
  eauto. }
  unfold AEvAtomHeap; fold AEvAtomHeap.
  sep pauto.
  unfold Get_heap; fold Get_heap.
  rewrite eq1; auto.

  unfold Get_heap in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eapply option2val in Hget;
  tryfalse.
  fold Get_heap in Hget.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevhpe in Hsat; eauto.
  sep pauto.
  3:{
  change ((a, char_t, v0) :: (x0 ++ (x, long, v) :: x1)) with 
    (((a, char_t, v0) :: x0) ++ ((x, long, v) :: x1)).
  eauto. }
  unfold AEvAtomHeap; fold AEvAtomHeap.
  sep pauto.
  unfold Get_heap; fold Get_heap.
  rewrite eq1; auto.

  unfold Get_heap in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eapply option2val in Hget;
  tryfalse.
  fold Get_heap in Hget.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevhpe in Hsat; eauto.
  sep pauto.
  3:{
  change ((a, Int16u, v0) :: (x0 ++ (x, long, v) :: x1)) with 
    (((a, Int16u, v0) :: x0) ++ ((x, long, v) :: x1)).
  eauto. }
  unfold AEvAtomHeap; fold AEvAtomHeap.
  sep pauto.
  unfold Get_heap; fold Get_heap.
  rewrite eq1; auto.
  
  unfold Get_heap in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget.
  eapply beq_tid_true_eq in eq1.
  subst a.
  eexists.
  instantiate (1:= nil).
  exists evhpe'.
  change ( nil ++ (x, long, v) :: evhpe') with ((x, long, v) :: evhpe').
  sep pauto.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep pauto.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep pauto.
  fold Get_heap in Hget.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevhpe in Hsat; eauto.
  sep pauto.
  3:{ 
    change ((a, long, v0) :: (x0 ++ (x, long, v) :: x1)) with 
      (((a, long, v0) :: x0) ++ ((x, long, v) :: x1)); eauto. }
  unfold AEvAtomHeap; fold AEvAtomHeap.
  sep pauto.
  unfold Get_heap.
  rewrite eq1.
  fold Get_heap; eauto.
  
  unfold Get_heap in Hget.
  destruct (os_inv.beq_addrval a x) eqn: eq1.
  eapply option2val in Hget;
  tryfalse.
  fold Get_heap in Hget.
  unfold AEvAtomHeap in Hsat; fold AEvAtomHeap in Hsat.
  sep normal in Hsat.
  sep lifts (3::4::nil)%nat in Hsat.
  eapply IHevhpe in Hsat.
  sep pauto.
  3:{
  change ((a, t ∗, v0) :: (x0 ++ (x, long, v) :: x1)) with
  (((a, t ∗, v0) :: x0) ++ ((x, long, v) :: x1)).
  eauto. }
  unfold AEvAtomHeap; fold AEvAtomHeap.
  sep pauto.
  unfold Get_heap; fold Get_heap.
  rewrite eq1; eauto.
  auto.
Qed.

Lemma AEvAtomHeap_succ_imp_alt :
  forall s a vll P, 
    s |= AEvAtomHeap (a :: vll) ** P ->
    s |= AEvAtomHeap (a::nil) ** AEvAtomHeap vll ** P.
Proof.
  intros.
  sep pauto.
  simpl AEvAtomHeap in *;
  destruct a. destruct p. destruct t;
  try(eapply astar_l_afalse_intro; sep pauto);
  sep pauto.
 Qed.

Lemma AEvAtomHeap_succ :
  forall s a vll, 
    s |= AEvAtomHeap (a::nil) ** AEvAtomHeap vll -> 
    s |= AEvAtomHeap (a :: vll).
Proof.
  intros.
  simpl AEvAtomHeap in *;
  destruct a. destruct p. destruct t;
  try(eapply astar_l_afalse_elim in H; sep pauto);
  sep pauto.
Qed.

Lemma AEvAtomHeap_compose :
  forall vll1 vll2 s, 
    s |= AEvAtomHeap vll1 ** AEvAtomHeap vll2 -> 
    s |= AEvAtomHeap (vll1 ++ vll2).
Proof.
  induction vll1; intros.
  simpl AEvAtomHeap in H.
  sep pauto.
  eapply AEvAtomHeap_succ_imp_alt in H.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  eapply AEvAtomHeap_succ.
  sep pauto.
Qed.

Lemma AEvAtomHeap_fold: 
  forall s x evheap P ident,
     s |= EX  v evh1 evh2,
                PV x @ Tint32 |-> v **
                LV ident @ (long) ∗ |-> Vptr x ** 
                [| evheap =(evh1 ++ (x, Tint32 , v) :: evh2) |] **
                [|rule_type_val_match Tint32 v = true|] ** (* new add *)
                AEvAtomHeap evh1 ** AEvAtomHeap evh2 ** P->
    s |=    AEvAtomHeap evheap **
               LV ident @ (long) ∗ |-> Vptr x  ** P.
Proof.
  intros.
  unfold AEvAtomHeap.
  sep pauto.
  fold AEvAtomHeap.
  apply AEvAtomHeap_compose.
  unfold AEvAtomHeap. fold AEvAtomHeap. 
  sep pauto.
Qed.

Lemma new_array_type_vallist_match_split2': 
  forall mqvl vll1 vll2 t, 
    new_array_type_vallist_match t mqvl ->
    mqvl = vll1 ++ vll2 ->
    new_array_type_vallist_match t vll1 /\
      new_array_type_vallist_match t vll2.
Proof.
  inductions mqvl.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0. 
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    simpl in Hmt1.
    destruct t;
      (destruct Hmt1 as (Hmta & Hmtb);
       specialize (IHmqvl vll1 vll2 _ Hmtb (eq_refl _));
       split; [simpl; simpljoin; auto | simpljoin; auto]).
Qed.

Lemma length6_ex:
  forall v'40 :list vallist,
    length v'40 = ∘ 6 ->
    exists v1 v2 v3 v4 v5 v6 ,
      v'40 = v1::v2::v3::v4::v5::v6::nil.
Proof.
  introv Hlen.
  try do 6  (destruct v'40; simpl in Hlen; tryfalse).
  do 6 eexists; eauto.
  assert (length v'40 = 0)%nat.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  inverts Hlen.
  auto.
  assert (v'40 = nil).
  destruct v'40.
  auto.
  simpl in H; tryfalse.
  subst.
  eauto.
Qed.

Lemma Get_heap_some_eq:
forall evheap addr a t v,
Get_heap evheap addr = Some (a, t , v) ->
a = addr.
Proof.
induction evheap; simpl; intros.
tryfalse.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a addr) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
inverts H; auto.
eapply IHevheap; eauto.
Qed.

Lemma Set_sval_eq:
forall vl1 vl2 t l v sval,
 Get_heap (vl1 ++ (sval, t, l) :: vl2) sval = Some (sval, t, l) ->
 Get_heap vl1 sval = None ->
 Set_sval (vl1 ++ (sval, t, l) :: vl2) sval v = vl1 ++ (sval, t, v) :: vl2.
Proof.
induction vl1; simpl; intros.
rewrite beq_tid_true in *.
auto.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a sval) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
tryfalse.
eapply IHvl1 in H0; eauto.
rewrite H0. auto.
Qed.

Lemma Get_Set_sval_eq:
forall vl t l l' sval,
 Get_heap vl sval = Some (sval, t, l) ->
 Get_heap (Set_sval vl sval l') sval = Some (sval, t, l').
Proof.
induction vl; simpl; intros.
tryfalse.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a sval) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
inverts H.
simpl.
rewrite beq_tid_true; auto.
simpl.
rewrite eq1.
eapply IHvl; eauto.
Qed.

Lemma Get_Set_sval_eq':
forall vl t l l' sval sval',
 os_inv.beq_addrval sval sval' = false ->
 Get_heap vl sval = Some (sval, t, l) ->
 Get_heap (Set_sval vl sval' l') sval = Some (sval, t, l).
Proof.
induction vl; simpl; intros.
tryfalse.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a sval) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
inverts H0.
rewrite H.
simpl.
rewrite beq_tid_true; auto.
destruct (os_inv.beq_addrval a sval') eqn: eq2.
eapply beq_tid_true_eq in eq2; subst.
simpl.
destruct (os_inv.beq_addrval sval' sval) eqn: eq3.
eapply beq_tid_true_eq in eq3; subst.
tryfalse.
auto.
simpl.
rewrite eq1.
eapply IHvl; eauto.
Qed.

Lemma Set_set_sval_eq:
forall vl v v' sval,
 Set_sval (Set_sval vl sval v) sval v' = Set_sval vl sval v'.
Proof.
induction vl; simpl; intros.
auto.
destruct a.
destruct p.
destruct (os_inv.beq_addrval a sval) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
simpl. rewrite beq_tid_true. auto.
simpl Set_sval at 1.
rewrite eq1.
rewrite IHvl. auto.
Qed.
