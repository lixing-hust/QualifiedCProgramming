Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.


Require Import partition.
Require Import abs_op_partition_ext.
Require Import ifun_spec.

(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.
Require Import symbolic_lemmas.
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.
Require Import evauxvar_lemmas.
Require Import language.
Require Import gjb_common.
Require Import pure.
Require Import os_inv.
Require Import os_code_defs.
Require Import abs_op.
Require Import os_inv.
Require Import inv_prop.
Require Import hoare_forward.
Require Import ev_aux_code.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import abs_infer_abt.
Require Import Lia.
Require Import pure_lib.
Require Import os_program.
Require Import partition_common.

Require Import os_ucos_h.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.
Open Scope list_scope.
 
Lemma initkis_absimp_range_abt:
  forall s sch ksize  v  P,
   (v <> Vint32 ksize ) ->  
    can_change_aop P -> 
    absinfer sch 
      (<|| (ksize_abt (| v::nil |) ;;  s)  ||>  ** HKsCurDomain ksize** P)
      (<|| ABORT ||> ** HKsCurDomain ksize** P).
Proof.
 intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= HKsCurDomain ksize ** P).
  pure_auto.
  instantiate (1:= ABORT).
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  pure_auto.  
  apply absinfer_seq_abt.
  pure_auto.
  pure_auto.
  auto.
  Unshelve. 
  exact None. 
Qed.
Lemma initksize_absimp_range_end_v:
  forall s sch ksize  v P ,
   (v = Vint32 ksize )->  
    can_change_aop P -> 
    absinfer sch 
      (<|| (ksize_abt (|  v ::nil |) ;;  s)  ||>  ** HKsCurDomain ksize  **  P)
      (<|| s ||> ** HKsCurDomain ksize **  P).
Proof.
  intros.
  simpljoin.
  subst.
  infer_solver 0%nat.
  Unshelve.
  exact None.
 
Qed.

Lemma initkis_cd_v1_abt:
  forall s sch ksize  v  cd  P,
   v = Vint32 cd  ->  
   cd= Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (cd_abt (| v ::nil |) ??  s)  ||>  ** HKsCurDomain ksize** P)
      (<|| ABORT  ||> ** HKsCurDomain ksize** P).
Proof.
  intros. subst.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
   2: eauto.
  can_change_aop_solver.
  eapply absinfer_abt; try pure_auto;
  absimp_abt_solver. can_change_aop_solver.
Qed.

Lemma new_get_ksdid_yes_end:
  forall sch domt  ksdid1  ksize v v1 P ,
      forall cr ksDSL  ksDL  dRdy  Dsch  Domc g h j ks,
     (v = Vint32 ksize /\ 0 <= Int.unsigned ksize < DOMAIN_SIZE)%Z  ->
        KsDomsMod.get  domt ksize = Some ks ->
        ks = (g, cr, ksDSL,  ksDL,  dRdy,  Dsch, Domc,  h, j) ->
         ksdid1 = cr ->
      v1 = Vint32 ksdid1->
    can_change_aop P -> 
    absinfer sch 
      (<|| (get_ksdid_yes (| v::v1 :: nil |))  ||> **  HKsDomains domt ** P)
      (<|| END (Some (Vint32 ksdid1)) ||> ** HKsDomains domt** P).
Proof.
intros.
  subst.
  infer_solver 0%nat.
 Unshelve.
Qed. 
Lemma new_get_ksdid_yes_abt:
  forall sch domt  ksdid1  ksize v  v1  P ,
      forall cr ksDSL  ksDL  dRdy  Dsch  Domc g h j ks,
     (v = Vint32 ksize /\ 0 <= Int.unsigned ksize < DOMAIN_SIZE)%Z  ->
        KsDomsMod.get  domt ksize = Some ks ->
        ks = (g, cr, ksDSL,  ksDL,  dRdy,  Dsch, Domc,  h, j) ->
         ksdid1 = cr ->
      v1 <> Vint32 ksdid1->
    can_change_aop P -> 
    absinfer sch 
      (<|| (get_ksdid_yes (| v::v1 :: nil |))  ||> **HKsDomains domt  ** P)
      (<|| ABORT ||> **HKsDomains domt ** P).
Proof.
 
intros. subst.
  eapply absinfer_abt; try pure_auto;
  absimp_abt_solver.  
  can_change_aop_solver.
Qed. 


Lemma  ksdom_plus':
  forall x x1 x2 s b i idx ,
     (length x <∘ 8)%nat ->
     (idx = length x)%nat ->
     s |= AKsDomains' (Vptr (b, i)) x ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) x1 domain_t **
       (EX l ,
      [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
        Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) x2 ** 
      [| array_type_vallist_match Tint8 x2 /\ length x2 = (nat_of_Z USER_INT_MAX_N)|] )
        ->
     s |= AKsDomains' (Vptr (b, i)) (x ++ (x1, x2) :: nil).
Proof.
  induction x.
  intros. 
  rewrite app_nil_l.
  rewrite H0 in H1.
  simpl length in *.
  rewrite Nat.mul_0_l in H1. 
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in H1.
  unfold AKsDomains' in *.
  eapply astar_r_aemp_elim.
  sep split. sep pauto; eauto.  intros.
  change ((a :: x) ++ (x1, x2) :: nil) with (a :: (x ++ (x1, x2) :: nil)).
  destruct a as [].
  unfold AKsDomains' in *. fold AKsDomains' in *.
  sep pauto.
   instantiate (1:= x4).
  sep cancel (Aarray x4 (Tarray char_t ∘ (* os_ucos_h. *)USER_INT_MAX_N) v0).

2:{ inverts H4. eauto. }
  simpl length in *.  inverts H4. 
 assert((length x < ∘ 8)%nat).
 {clear - H. mauto.  } 
  lets Hx' : IHx H4. eapply Hx'. eauto.
assert(x3 +ᵢ  $ Z.of_nat (S (length x) * typelen domain_t) = (x3 +ᵢ  $ Z.of_nat (typelen domain_t)) +ᵢ
        $ Z.of_nat (length x * typelen domain_t)).
{ assert(forall n m:nat ,( (S n) * m = n * m + m)%nat).
  clear - H0.
  intros. mauto.
  rewrite H8.
  rewrite Int.add_assoc.
  unfold cpu_conf_t.
  clear - H.
  simpl.
  destruct (length x). simpl. auto.
  destruct ( n). auto. destruct n0; auto. destruct n0; auto. destruct n0; auto. 
  destruct n0; auto. destruct n0; auto. destruct n0; auto. destruct n0; auto.
  simpl in H. assert(Pos.to_nat 8 = 8%nat). mauto.
  rewrite H0 in H.  clear - H.
  assert((S(S (S (S (S (S (S (S (S n0)))))))) > 8)%nat). mauto. mauto. }
  rewrite <- H8.
  sep pauto.
Qed. 

Lemma Aksdom_plus_frm: 
 forall x x1 x2 s b i idx P,
     (length x < ∘ 8)%nat ->
     (idx = length x)%nat ->
     s |= AKsDomains' (Vptr (b, i)) x ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) x1 domain_t **
       (EX l ,
      [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
        Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) x2 ** 
      [| array_type_vallist_match Tint8 x2 /\ length x2 = (nat_of_Z USER_INT_MAX_N)|] )**P
        ->
     s |= AKsDomains' (Vptr (b, i)) (x ++ (x1, x2) :: nil)**P.
Proof. 
  intros . 
  sep cancel P. 
  eapply ksdom_plus'; eauto.
Qed.  

Lemma Aksdom_unfold_any_idx: 
   forall idx s vll b i ,
    s |= AKsDomains' (Vptr (b,i)) vll ->
     length vll= ∘ (DOMAIN_SIZE) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl' ,
           AKsDomains' (Vptr (b, i)) vll1 ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
       (EX l ,
      [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
        Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
      [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|] )**
          AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2 **
          [| vll = vll1 ++ ((vl, vl')::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) . 
Proof.
  induction idx; introv Hsat Hlen Hlt.
  rewrite Nat.mul_0_l. rewrite Nat.mul_1_l.
  destruct vll; simpl length in *.
  tryfalse.
  destruct d as [].
  unfold AKsDomains' in Hsat. fold AKsDomains' in Hsat.
  change ($ Z.of_nat 0) with Int.zero.
  rewrite Int.add_zero.
  sep normal in Hsat; sep destruct Hsat.
  exists (nil: list Doamin_t_val) vll v v0 .
  simpl AKsDomains' at 1.   
  sep split in Hsat. inverts H.
  rewrite app_nil_l. simpl length.
  sep pauto; eauto.
  auto with zarith.
  split; auto.
  assert (Heq: Z.of_nat (S (length vll))  = Z.of_nat (length vll) +  Z.of_nat 1).
  {  auto with zarith. }
  rewrite Heq. 

  rewrite Zplus_minus.
  rewrite nat_of_Z_of_nat. auto.
  lets Hsat': Hsat. eapply IHidx in Hsat.
  2: { eauto.  }
  2: { eapply NPeano.Nat.lt_succ_l.
  eauto.  }
  clear IHidx Hsat' .
  sep normal in Hsat; sep destruct Hsat.
  destruct x0.
   exists ( (x ++ (x1, x2) :: nil) : list Doamin_t_val)   (nil: list Doamin_t_val) 
  (nil: vallist) (nil: list val) .
  simpl AKsDomains' at 1.
  sep split in Hsat. destruct H2 as (Hidx & Hlt1).
  eapply z_split in H3.
  destruct H3 as [Heq | Hltt].
  eapply Nat2Z.inj in Heq.
  rewrite Heq in Hlt.
  clear - Hlt. int auto. 
  rewrite Hlen in Hlt1, Hlt.
  change (∘ DOMAIN_SIZE) with 8%nat in Hlt1, Hlt.
  change (length nil) with 0%nat in Hlt1.
  pure_auto.
  rewrite Hlen in Hltt.
  change (∘ DOMAIN_SIZE) with 8%nat in Hltt.
  assert(Hss:(Z.of_nat (8 - (S idx)) = Z.of_nat 8 - Z.of_nat (S idx))).
  eapply Nat2Z.inj_sub; eauto.
  clear -Hlt.  eapply Nat.lt_le_incl; eauto.
  rewrite <-Hss in Hlt1.
  rewrite nat_of_Z_of_nat in Hlt1.
  eapply Nat.sub_gt in Hlt. rewrite <- Hlt1 in Hlt. tryfalse.

  destruct d as [].
  unfold AKsDomains' in Hsat. fold AKsDomains' in Hsat.
  sep normal in Hsat; sep destruct Hsat.
  sep split in Hsat.
  simpljoin.
  remember (i +ᵢ  $ Z.of_nat (S (length x) * typelen domain_t)) as i_idx.
  inverts H.
  exists ((  x ++ (x1, x2) ::nil) : list Doamin_t_val) . 
  exists (x0: list Doamin_t_val).
  exists (v:vallist).
  exists (v0:list val).
  eapply Aksdom_plus_frm.
  {
  clear - Hlen Hlt.
  rewrite Hlen in Hlt.
  change (∘ DOMAIN_SIZE) with 8%nat in *.
  change (∘ 8) with 8%nat.
  auto with zarith.
  }
  eauto.
  assert (Heq: 
               (i +ᵢ  $ Z.of_nat (S (length x) * typelen domain_t)) +ᵢ
               $ Z.of_nat (typelen domain_t) 
      = i +ᵢ  $ Z.of_nat (S (S (length x)) * typelen domain_t) ).
 { rewrite Int.add_assoc.
    assert (Heq2: ($ Z.of_nat (S (length x) * typelen domain_t) +ᵢ
  $ Z.of_nat (typelen domain_t)) = $ Z.of_nat (S (S (length x)) * typelen domain_t)).
   { simpl typelen.
      rewrite Hlen in Hlt.
      clear -Hlt.
      change (∘ DOMAIN_SIZE) with 8%nat in *.
      int auto.
   }
  rewrite Heq2; auto.
  }
  rewrite <- Heq.
  sep pauto; eauto.
  rewrite Hlen in *.
  clear -Hlt. auto with zarith. 
  split.
  rewrite app_length. simpl. auto with zarith.
  simpl length in*.
  eapply eq_add_S.
  rewrite H7.
  rewrite Hlen.
  rewrite Hlen in Hlt.
  clear -Hlt.
  change (∘ DOMAIN_SIZE) with (8%nat) in *.
  unfold nat_of_Z.
  auto with zarith. 
  eapply list_cons_assoc.

Qed.

Lemma Aksdom_unfold_any_idx_frm: 
  forall idx s vll b i P,
    s |= AKsDomains' (Vptr (b,i)) vll ** P->
     length vll= ∘ (DOMAIN_SIZE) ->
    (idx < length vll)%nat ->
    s |= (EX vll1 vll2 vl  vl' ,
           AKsDomains' (Vptr (b, i)) vll1 ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
       (EX l ,
      [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
        Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
      [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|] )**
          AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2 **
          [| vll = vll1 ++ ((vl, vl')::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (Z.of_nat(length vll) - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= Z.of_nat(length vll) |]) ** P. 
Proof. 
  intros. 
  sep cancel P.
  eapply Aksdom_unfold_any_idx; eauto.
Qed.  

Lemma Aksdom_compose_strong:
 forall  vll1 vll2 s b i idx    ,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |= AKsDomains' (Vptr (b, i)) vll1 ** 
             AKsDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_t))))) vll2->
     s |= AKsDomains' (Vptr (b, i)) (vll1++vll2) .
Proof.
  induction vll1. intros.
  rewrite app_nil_l.
  rewrite <- H in H1.  
  simpl length in *.
  unfold AKsDomains' in *. fold AKsDomains' in *.
  sep pauto.
  rewrite Nat.mul_0_l in H1.
  change ($ Z.of_nat 0) with Int.zero in *.
  rewrite Int.add_zero in H1. eauto.   
 
   intros.
   change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)). 
   destruct a as []. 
   unfold AKsDomains' in *. fold AKsDomains' in *.

  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  inverts H2.
  sep pauto. instantiate (1:= x1).
  do 1 sep cancel 1%nat 1%nat.
  eapply IHvll1.
 
  eauto.
  simpl length in H0.
  auto with zarith.
  rewrite Int.add_assoc.
  simpl length in *.
  assert (Heq: ($ Z.of_nat (typelen domain_t) +ᵢ
         $ Z.of_nat (length vll1 * typelen domain_t)) 
          = $ Z.of_nat (S (length vll1) * typelen domain_t)).
  clear -H0.
  simpl typelen.
  change (∘ DOMAIN_SIZE) with 8%nat in *.
  int auto.
  rewrite Heq.
  auto.
  eauto. 
Qed.

Lemma Aksdom_compose_strong_frm:
 forall  vll1 vll2 s b i idx  P,
    ( length vll1 = idx)%nat -> 
    ( idx < ∘ (DOMAIN_SIZE))%nat ->
     s |= AKsDomains' (Vptr (b, i)) vll1 ** 
             AKsDomains'  (Vptr (b, (i+ᵢ  $ Z.of_nat ( idx* (typelen domain_t))))) vll2 ** P->
     s |= AKsDomains' (Vptr (b, i)) (vll1++vll2)  **P.
Proof.
 intros. 
  sep cancel P.
  eapply Aksdom_compose_strong; eauto.
Qed.  

Lemma Aksdom_select_sn_strong :
 forall idx s b i P vll1 vll2 vl  vl' ,
    ( length vll1 = idx)%nat ->
    ( idx < ∘ (DOMAIN_SIZE))%nat -> 
    s |= AKsDomains' (Vptr (b, i)) vll1 ** 
           node_offt (Vptr (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t)))) vl domain_t **
       (EX l ,
      [| id_addrval (b, i +ᵢ $ Z.of_nat (idx * (typelen domain_t))) domainIntStatusTbl domain_t = Some l |] **
        Aarray l (Tarray Tint8 (nat_of_Z USER_INT_MAX_N)) vl' ** 
      [| array_type_vallist_match Tint8 vl' /\ length vl' = (nat_of_Z USER_INT_MAX_N)|] )**
          AKsDomains' (Vptr (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen domain_t))))) vll2 **  P->
     s |= AKsDomains'(Vptr (b, i)) (vll1 ++  ((vl, vl')::vll2)) ** P. 
Proof.
   induction vll2.  intros.
  unfold AKsDomains' in *. fold AKsDomains'  in *.
  eapply Aksdom_plus_frm .
   {
  clear - H H0.
  rewrite <- H in H0.
  change (∘ DOMAIN_SIZE) with 8%nat in *.
  change (∘ 8) with 8%nat.
  auto with zarith.
  }
  eauto.
  sep cancel (AKsDomains' (Vptr (b, i)) vll1).
  sep pauto.
   intros.
  unfold AKsDomains' in *. fold AKsDomains'  in *. 


   eapply Aksdom_compose_strong_frm .
   eauto.
   eauto.
   destruct a as []. 
   unfold AKsDomains' in *. fold AKsDomains' in *.
   sep normal in H1.
   sep destruct H1.
   sep split in H1.
   simpljoin.
   assert (Heq:( i +ᵢ  $ Z.of_nat (S (length vll1) * typelen domain_t)) = ( (
        (i +ᵢ  $ Z.of_nat (length vll1 * typelen domain_t)) +ᵢ
        $ Z.of_nat (typelen domain_t)))).
{ assert(forall n m:nat ,( (S n) * m = n * m + m)%nat).
  clear - H0.
  intros. mauto.
  rewrite H.
  rewrite Int.add_assoc.
  unfold cpu_conf_t.
  clear - H0.
  simpl.
  change (∘ DOMAIN_SIZE) with 8 %nat in *.
  int auto.
  do 2 try rewrite Int.unsigned_repr; try int auto.
   }
   rewrite Heq in *.
 sep pauto.
Qed.
Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Lemma AksDomains_P_split:
forall vll1 vll2 (absc: KsDomsMod.map) n,
  AKsDomains_P (Vint32 n) (vll1 ++ vll2) absc ->
  (length vll1 < ∘ DOMAIN_SIZE)%nat ->
  exists absc1 absc2 idx,
  idx = (length vll1)%nat /\
  AKsDomains_P (Vint32 n) vll1 absc1 /\
  AKsDomains_P (Vint32 (Int.add n (Int.repr (Z.of_nat idx )))) vll2 absc2 /\
  KsDomsMod.join absc1 absc2 absc.
Proof.
  induction vll1. intros. 
  rewrite app_nil_l in H.
  do 4 eexists. 
  simpl length in *.
  eauto.
  change ($ Z.of_nat 0) with Int.zero.
  rewrite Int.add_zero.
  simpl AKsDomains_P.
  splits; eauto.
  eapply KsDomsMod.join_comm.
  eapply KsDomsMod.map_join_emp; eauto.

   intros.
   rename H0 into Hlen.
   change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in *. 
   unfold AKsDomains_P in H; fold AKsDomains_P in H.
   mytac.
   inverts H.
   eapply IHvll1 in H3; eauto.
   simpljoin.
   unfold TcbJoin in H1.
   eapply KsDomsMod.join_comm in H1, H4.
   lets Hnew: KsDomsMod.map_join_assoc H4 H1.
   simpljoin.
   simpl AKsDomains_P.
   simpl length.
   eapply KsDomsMod.join_comm in H5,H.
   repeat eexists; eauto.
   assert (Heq: (x +ᵢ  $ Z.of_nat (S (length vll1))) = ((x +ᵢ  Int.one) +ᵢ  $ Z.of_nat (length vll1))).
   { rewrite Int.add_assoc.
      assert (Heq1: $ Z.of_nat (S (length vll1)) = (Int.one +ᵢ  $ Z.of_nat (length vll1))).
      { clear -Hlen.
        simpl length in *.
        change (∘ DOMAIN_SIZE) with 8%nat in *. 
        int auto.
       }
       rewrite Heq1. auto.
   }
   rewrite Heq. auto.
   simpl length in *.
   change (∘ DOMAIN_SIZE) with 8%nat in *. 
   auto with zarith.
Qed.


Lemma AksDomains_P_split':
forall vll1 vl vll2 (absc: KsDomsMod.map) n,
  AKsDomains_P (Vint32 n) (vll1 ++ (vl :: vll2)) absc ->
  (length vll1 < ∘ DOMAIN_SIZE) %nat ->
  exists absc1 absc2 absc0 abcs' idx,
  idx = (length vll1)%nat /\
  AKsDomains_P (Vint32 n) vll1 absc1 /\
  AKsDomains_P (Vint32(Int.add n (Int.repr ((Z.of_nat idx) + 1)%Z))) vll2 absc2 /\
  AKsDomains_P (Vint32(Int.add n (Int.repr (Z.of_nat idx ))))(vl :: nil) (KsDomsMod.sig (Int.add n (Int.repr (Z.of_nat idx))) absc0) /\
  TcbJoin (Int.add n (Int.repr (Z.of_nat idx))) absc0 absc2 abcs' /\
  KsDomsMod.join absc1 abcs' absc.
Proof.
  intros.
  eapply AksDomains_P_split in H.
  2: eauto.
  simpljoin.
  simpl AKsDomains_P in H2.
  simpljoin.
  inverts H.
  simpl AKsDomains_P.
  repeat eexists; eauto.
   assert (Heq: (Vint32 ((n +ᵢ  $ Z.of_nat (length vll1)) +ᵢ  Int.one)) = (Vint32 (n +ᵢ  $ (Z.of_nat (length vll1) + 1)))).
   { rewrite Int.add_assoc.
      assert (Heq1: $ (Z.of_nat  (length vll1)+1) = ($ Z.of_nat (length vll1) +ᵢ  Int.one)).
      { clear -H0.
        simpl length in *.
        change (∘ DOMAIN_SIZE) with 8%nat in *. 
        int auto.
       }
       rewrite Heq1. auto.
   }
  rewrite Heq in H6. auto.
  eapply KsDomsMod.map_join_emp; eauto.
Qed.

Lemma DomTjoin_get_a_my:
  forall x v m' m,
    TcbJoin x v m' m ->
    KsDomsMod.get m x = Some v.
Proof.
  intros x v m' m.
  eapply KsDomsMod.join_sig_get.
Qed.

Lemma DomTjoin_get_a :
  forall x a x1 tcbls,
    TcbJoin x a  x1 tcbls ->
    KsDomsMod.get tcbls x = Some a.
Proof.
  intros x a x1 tcbls.
  apply DomTjoin_get_a_my.
Qed.

Lemma intlt2nat: forall x y, Int.unsigned x < y -> (Z.to_nat (Int.unsigned x) < Z.to_nat y)%nat.
Proof.
  intros.
  assert (y=y-1+1).
  mauto.
  rewrite H0.
  apply int_unsigned_le_z2nat_lt.
  mauto.
Qed.
Theorem can_change_aop_AisCoreBoot :
  forall x1 ,
can_change_aop (AisCoreBoot x1 ).
Proof.
unfold AisCoreBoot in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AisCoreBoot : can_change_aop.

Theorem can_change_aop_AsystemStck' :
  forall x1 ,
can_change_aop (AsystemStck' x1 ).
Proof.
unfold AsystemStck' in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AsystemStck' : can_change_aop.


Theorem can_change_aop_AOSSystemSP :
  forall x1 ,
can_change_aop (AOSSystemSP x1 ).
Proof.
unfold AOSSystemSP in *. intros.
can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSSystemSP : can_change_aop.

Lemma getPartitionIDAProof:
  forall tid vl p r,
    Some p =
      BuildPreA' os_api getPartitionID
              (getPartitionID_pos , (Tint8, nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api getPartitionID
              (getPartitionID_pos , (Tint8, nil)) vl OSLInv tid init_lg -> 
    exists t d1 d2 s,
      os_api getPartitionID = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 3 (destruct v'; try apply absabort_rule).
  hoare forward prim.
  unfold PartitionInv. 
  hoare unfold.

  assert(Hor: (v <> Vint32 v'53 \/ v = Vint32 v'53 )) by tauto.
  destruct Hor as [Hn | He].
  hoare_lifts_trms_pre (Aop, kscurdom).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initkis_absimp_range_abt; eauto. eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule.
   hoare_lifts_trms_pre (Aop, kscurdom).
  hoare abscsq.
  apply noabs_oslinv. 
  
  eapply initksize_absimp_range_end_v. eauto.
  can_change_aop_solver.
  unfold AKsCurDomain. 

  hoare forward.  
  hoare_split_pure_all.
   hoare_lifts_trms_pre (Aop, kscurdom).
  hoare forward prim.

  unfold PartitionInv, AKsCurDomain.
  sep pauto;eauto.
  sep cancel AucosConf.
  sep cancel Adomain2index.
  sep cancel AKsDomSchedule.
  sep cancel AisChangePartion.  
  sep cancel AIntPartMux.
  sep cancel AKsDomains.
  sep cancel AisCoreBoot.
  sep cancel ARootTaskStk.
  sep cancel CoreCommuInv. 
  sep cancel p_local. 
  sep cancel EvtInv. 

sep cancel ACorepartnum.
sep cancel AsystemStck'.
sep cancel AOSSystemSP.

sep cancel APartArea.
sep cancel APartID2Dom.
sep cancel APthreadAttr.
sep cancel AOSDomainPortPtrList.
sep cancel AOSKernelPortIDTbl.
sep cancel AOSChannelIDTbl.
sep cancel AOSKernelPortFreeList.
sep cancel AOSChannelFreeList.
sep cancel OtherPortPtrList.
sep cancel AOSCorePortPtrList.
sep cancel AOSPortAttrTbl'.
sep cancel CapabilityInv.

  2: eauto.
sep cancel Aier.  
eauto. pure_auto.
pure_auto.
 hoare forward prim.

destruct H12.
2:{
unfold PartitionInv.
unfold AKsDomains.
  hoare unfold.
 hoare_lifts_trms_pre (Aop, kscurdom).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initkis_cd_v1_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  eapply absabort_rule. }
   
unfold PartitionInv.
unfold AKsDomains.   hoare unfold. 
  destruct v'140. 
  eapply backward_rule1.  introv Hsat.
  sep_lifts_trms_in Hsat AKsDomains'.
  eapply Aksdom_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned v'53)) ; eauto.

  {  rewrite H13.  unfold nat_of_Z.  mauto. } 
  unfold node_offt.
  hoare unfold.
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar with (v2:=Vint32 i2).
  
  split; introv Hsat. sep cancel (Alvarmapsto ksdid1). eauto.
  sep auto. 
   instantiate (1:=char_t).
  2: { apply eq_int. splits. eauto. eauto.  }
  2: { sep pauto.   sep_lift_context_in H32 p_local.
         instantiate (1:=(logic_val (V$ 1)
           :: logic_val (V$ inferules.__EvLoc_normal)
              :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil)). sep pauto. } 
  introv Hsat. 
  (* sep_lift_context_in H8 Astruct. *)  (* simpl in H8. *)
   assert (H00 := Hsat).
  sep lift 5%nat in H00.
  Require Import gjb_common.
 
Ltac sep_get_rv_array_struct_gen :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        introv Hsat;
        eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  | Hsat:?s |= ?P
    |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
       eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply gjb_common.int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  end.

sep_get_rv_array_struct_gen.
simpl.  splits; eauto.
  change (Byte.max_unsigned) with 255. clear - H38. mauto.
 change (Byte.max_unsigned) with 255. clear - H44. mauto.
 change (Byte.max_unsigned) with 255. clear - H45. mauto.
(*   sep_get_rv_array_struct. *) 

  eapply backward_rule1. intros.
  eapply Aksdom_select_sn_strong with (b:= v'144) (i := i) (idx := (Z.to_nat (Int.unsigned v'53))); eauto. 
  (* clear -l0. *)
  change (∘ DOMAIN_SIZE) with 8%nat in *.  
  change ( DOMAIN_SIZE) with 8 in *. 
  auto with zarith.
  unfold node_offt.
  sep pauto; eauto.
  sep cancel AKsDomains'.
  sep cancel Aarray.
  sep cancel Astruct.
  eauto.
  split; auto. pure_auto. 
 (*  hoare forward. *)
  lets Hcp: H15.
  eapply AksDomains_P_split' in H15; eauto.
 2: {(* clear -H12 l0 H1. *) change (∘ DOMAIN_SIZE) with 8%nat.   
    eapply intlt2nat in H29. rewrite <- H34 in H29. eauto. }
  destruct H15 as (abscpus1 & abscpus2 & abscpus0 & abcspus' & idx 
  & Hidx & Hcpu1 & Hcpu2 & Hcpu3 & Htcbj & Hcpum). 
  rewrite H34 in Hidx.
  rewrite Hidx in *.
  lets Htcbj': Htcbj.
  eapply DomTjoin_get_a in Htcbj.
  destruct abscpus0. destruct p. destruct p. destruct p. destruct p. destruct p. destruct p. destruct p.
  eapply KsDomsMod.join_get_get_r in Hcpum; eauto.
  assert(Heq1: ($ Z.of_nat (Z.to_nat (Int.unsigned v'53))) = v'53).
  {eapply nat_elim; eauto.  }
  rewrite Heq1 in Hcpum.

  lets Hcp': Hcpu3.
  simpl in Hcp'.
  simpljoin.
  inverts H15.
  apply KsDomsMod.join_comm in H33.
  apply KsDomsMod.join_emp_eq in H33.
  inverts H33.
  destruct H40 as (Hhl1 & Hhl2).
  funfold Hhl1. funfold Hhl2.

  assert(Htr: (v0 <>  Vint32 d6 \/ v0 = Vint32 d6 )) by tauto.
  destruct Htr as [Hnn | Hne].
  hoare_lifts_trms_pre (Aop, ksdoms).
  eapply abscsq_rule.
  apply noabs_oslinv.
  rewrite Int.add_zero_l in Htcbj'. 
  rewrite Int.add_zero_l in Hcpum.



eapply absinfer_choice2; eauto.
  can_change_aop_solver.
  can_change_aop_solver.
eapply absinfer_eq.
   hoare_lifts_trms_pre (Aop, ksdoms).
  hoare abscsq.
  apply noabs_oslinv. 
rewrite Int.add_zero_l in Htcbj'. 
  rewrite Int.add_zero_l in Hcpum.


  eapply new_get_ksdid_yes_abt; eauto.  eauto.
  can_change_aop_solver.
(*   eapply absinfer_eq. *)
  eapply absabort_rule.
   hoare_lifts_trms_pre (Aop, ksdoms).
  hoare abscsq.
  apply noabs_oslinv. 
  rewrite Int.add_zero_l in Htcbj'. 
  rewrite Int.add_zero_l in Hcpum.

eapply absinfer_choice2; eauto.
  can_change_aop_solver.
  can_change_aop_solver.
(* eapply absinfer_eq. *)
   hoare_lifts_trms_pre (Aop, ksdoms).
  hoare abscsq.
  apply noabs_oslinv. 
rewrite Int.add_zero_l in Htcbj'. 
  rewrite Int.add_zero_l in Hcpum.
  eapply new_get_ksdid_yes_end; eauto.
  can_change_aop_solver. subst.

hoare forward prim.
  sep cancel EvtInv. 
 sep cancel CoreCommuInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier. 
  unfold PartitionInv, AKsCurDomain. 
  unfold AKsDomains.
  unfold AKsCurDomain in H33.
  sep pauto; eauto.
  sep cancel AucosConf.
  sep cancel Adomain2index.
  sep cancel AKsDomSchedule.
  sep cancel AisChangePartion.  
  sep cancel AIntPartMux.
  sep cancel AKsDomains'.

sep cancel AisCoreBoot.
sep cancel AsystemStck'.
sep cancel AOSSystemSP.
sep cancel ARootTaskStk.
  sep cancel ACorepartnum.
sep cancel APartArea.
sep cancel APartID2Dom.
sep cancel APthreadAttr.
sep cancel AOSDomainPortPtrList.
sep cancel AOSKernelPortIDTbl.
sep cancel AOSChannelIDTbl.
sep cancel AOSKernelPortFreeList.
sep cancel AOSChannelFreeList.
sep cancel OtherPortPtrList.
sep cancel AOSCorePortPtrList.
sep cancel AOSPortAttrTbl'.
sep cancel CapabilityInv.

  eauto.
  auto.
  pure_auto.
  subst.
  hoare forward. 

  clear - H38.
  destruct   (Int.unsigned d6 <=? Byte.max_unsigned) eqn:H. auto.
  eapply Z.leb_gt in H.
  change (Byte.max_unsigned) with 255 in H.
  lia.
Unshelve.
  exact O.

Qed.

   
