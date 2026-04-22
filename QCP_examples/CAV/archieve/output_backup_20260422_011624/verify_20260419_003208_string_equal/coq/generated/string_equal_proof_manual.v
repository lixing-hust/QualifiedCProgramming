Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260419_003208_string_equal Require Import string_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_equal.
Local Open Scope sac.

Lemma Znth_app_zero :
  forall (l : list Z),
    Znth (Zlength l) (app l (cons 0 nil)) 0 = 0.
Proof.
  intro l.
  rewrite app_Znth2.
  - replace (Zlength l - Zlength l) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
  - lia.
Qed.

Lemma app_Znth_nonzero_lt :
  forall (l : list Z) (i : Z),
    i <= Zlength l ->
    Znth i (app l (cons 0 nil)) 0 <> 0 ->
    i < Zlength l.
Proof.
  intros l i Hle Hnz.
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hlt | Hge].
  - exact Hlt.
  - assert (Hi : i = Zlength l) by lia.
    subst i.
    rewrite Znth_app_zero in Hnz.
    contradiction.
Qed.

Lemma first_zero_at_end :
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    (forall (k : Z), 0 <= k -> k < n -> Znth k l 0 <> 0) ->
    0 <= i ->
    i <= n ->
    Znth i (app l (cons 0 nil)) 0 = 0 ->
    i = n.
Proof.
  intros l n i Hlen Hnz Hi0 Hile Hzero.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
  - rewrite app_Znth1 in Hzero by (rewrite Hlen; lia).
    specialize (Hnz i Hi0 Hlt).
    contradiction.
  - lia.
Qed.

Lemma string_equal_spec_sym :
  forall (la lb : list Z),
    string_equal_spec la lb = string_equal_spec lb la.
Proof.
  induction la.
  - intros lb.
    destruct lb.
    + reflexivity.
    + reflexivity.
  - intros lb.
    destruct lb.
    + reflexivity.
    + simpl.
      rename z into b.
      destruct (Z.eq_dec a b) as [Hab | Hab].
      * subst b.
        destruct (Z.eq_dec a a) as [_ | Hneq].
        2: contradiction.
        exact (IHla lb).
      * destruct (Z.eq_dec b a) as [Hba | Hba].
        -- exfalso. apply Hab. symmetry. exact Hba.
        -- reflexivity.
Qed.

Lemma string_equal_spec_mismatch :
  forall (la lb : list Z) (i : Z),
    0 <= i ->
    i < Zlength la ->
    i < Zlength lb ->
    Znth i la 0 <> Znth i lb 0 ->
    (forall (j : Z), 0 <= j -> j < i -> Znth j la 0 = Znth j lb 0) ->
    string_equal_spec la lb = 0.
Proof.
  induction la.
  - intros lb i Hi0 Hiltla Hiltlb Hneq Hpref.
    rewrite Zlength_nil in Hiltla. lia.
  - intros lb i Hi0 Hiltla Hiltlb Hneq Hpref.
    destruct lb.
    + rewrite Zlength_nil in Hiltlb. lia.
    + rename z into b.
      destruct (Z.eq_dec a b) as [Hab | Hab].
      * subst b.
        simpl.
        destruct (Z.eq_dec a a) as [_ | Hcontra].
        2: contradiction.
        assert (Hi_cases : i = 0 \/ 0 < i) by lia.
        destruct Hi_cases as [Hi_eq | Hi_gt].
        -- subst i.
           rewrite !Znth0_cons in Hneq.
           contradiction.
        -- apply IHla with (i := i - 1).
           ++ lia.
           ++ rewrite Zlength_cons in Hiltla.
              pose proof Zlength_nonneg la.
              lia.
           ++ rewrite Zlength_cons in Hiltlb.
              pose proof Zlength_nonneg lb.
              lia.
           ++ rewrite !Znth_cons in Hneq by lia.
              exact Hneq.
           ++ intros j Hj0 Hjlt.
              specialize (Hpref (j + 1)).
              assert (Hj1_nonneg : 0 <= j + 1) by lia.
              assert (Hj1_lt : j + 1 < i) by lia.
              specialize (Hpref Hj1_nonneg Hj1_lt).
              rewrite !Znth_cons in Hpref by lia.
              replace (j + 1 - 1) with j in Hpref by lia.
              exact Hpref.
      * simpl.
        destruct (Z.eq_dec a b) as [Hcontra | _].
        -- contradiction.
        -- reflexivity.
Qed.

Lemma string_equal_spec_equal :
  forall (la lb : list Z),
    Zlength la = Zlength lb ->
    (forall (j : Z), 0 <= j -> j < Zlength la -> Znth j la 0 = Znth j lb 0) ->
    string_equal_spec la lb = 1.
Proof.
  induction la.
  - intros lb Hlen Hall.
    destruct lb.
    + reflexivity.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg lb.
      lia.
  - intros lb Hlen Hall.
    destruct lb.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg la.
      lia.
    + rename z into b.
      assert (Hab : a = b).
      {
        specialize (Hall 0).
        assert (Hlt : 0 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall (Z.le_refl 0) Hlt).
        rewrite !Znth0_cons in Hall.
        exact Hall.
      }
      subst b.
      simpl.
      destruct (Z.eq_dec a a) as [_ | Hcontra].
      2: contradiction.
      apply IHla.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros j Hj0 Hjlt.
        specialize (Hall (j + 1)).
        assert (Hj1_nonneg : 0 <= j + 1) by lia.
        assert (Hj1_lt : j + 1 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall Hj1_nonneg Hj1_lt).
        rewrite !Znth_cons in Hall by lia.
        replace (j + 1 - 1) with j in Hall by lia.
        exact Hall.
Qed.

Lemma string_equal_spec_left_shorter :
  forall (la lb : list Z),
    Zlength la <= Zlength lb ->
    (forall (j : Z), 0 <= j -> j < Zlength la -> Znth j la 0 = Znth j lb 0) ->
    Znth (Zlength la) lb 0 <> 0 ->
    string_equal_spec la lb = 0.
Proof.
  induction la.
  - intros lb Hlen Hall Hnext.
    destruct lb.
    + simpl in Hnext. contradiction.
    + reflexivity.
  - intros lb Hlen Hall Hnext.
    destruct lb.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg la.
      lia.
    + rename z into b.
      assert (Hab : a = b).
      {
        specialize (Hall 0).
        assert (Hlt : 0 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall (Z.le_refl 0) Hlt).
        rewrite !Znth0_cons in Hall.
        exact Hall.
      }
      subst b.
      simpl.
      destruct (Z.eq_dec a a) as [_ | Hcontra].
      2: contradiction.
      apply IHla.
      * rewrite !Zlength_cons in Hlen.
        pose proof Zlength_nonneg la.
        pose proof Zlength_nonneg lb.
        lia.
      * intros j Hj0 Hjlt.
        specialize (Hall (j + 1)).
        assert (Hj1_nonneg : 0 <= j + 1) by lia.
        assert (Hj1_lt : j + 1 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall Hj1_nonneg Hj1_lt).
        rewrite !Znth_cons in Hall by lia.
        replace (j + 1 - 1) with j in Hall by lia.
        exact Hall.
      * rewrite Zlength_cons in Hnext.
        assert (Hidx_pos : Zlength la + 1 > 0).
        {
          pose proof Zlength_nonneg la.
          lia.
        }
        rewrite Znth_cons in Hnext by exact Hidx_pos.
        replace (Z.succ (Zlength la) - 1) with (Zlength la) in Hnext by lia.
        exact Hnext.
Qed.

Lemma string_equal_spec_zero_nonzero :
  forall (la lb : list Z) (i : Z),
    0 <= i ->
    i <= Zlength la ->
    i <= Zlength lb ->
    Znth i (app la (cons 0 nil)) 0 = 0 ->
    Znth i (app lb (cons 0 nil)) 0 <> 0 ->
    (forall (j : Z), 0 <= j -> j < i -> Znth j la 0 = Znth j lb 0) ->
    string_equal_spec la lb = 0.
Proof.
  intros la lb i Hi0 Hile_la Hile_lb Hzero Hnonzero Hpref.
  destruct (Z_lt_ge_dec i (Zlength la)) as [Hlt_la | Hge_la].
  - assert (Hlt_lb : i < Zlength lb).
    { eapply app_Znth_nonzero_lt; eauto. }
    assert (Hi_range_la : 0 <= i < Zlength la) by lia.
    assert (Hi_range_lb : 0 <= i < Zlength lb) by lia.
    rewrite app_Znth1 in Hzero by exact Hi_range_la.
    rewrite app_Znth1 in Hnonzero by exact Hi_range_lb.
    eapply string_equal_spec_mismatch.
    + exact Hi0.
    + exact Hlt_la.
    + exact Hlt_lb.
    + intro Heq_i.
      apply Hnonzero.
      rewrite <- Heq_i.
      exact Hzero.
    + exact Hpref.
  - assert (Hi_eq : i = Zlength la) by lia.
    subst i.
    assert (Hlt_lb : Zlength la < Zlength lb).
    { eapply app_Znth_nonzero_lt; eauto. }
    assert (Hi_range_lb : 0 <= Zlength la < Zlength lb) by lia.
    rewrite app_Znth1 in Hnonzero by exact Hi_range_lb.
    eapply string_equal_spec_left_shorter.
    + lia.
    + exact Hpref.
    + exact Hnonzero.
Qed.

Lemma proof_of_string_equal_entail_wit_1 : string_equal_entail_wit_1.
Proof.
  unfold string_equal_entail_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_string_equal_entail_wit_2 : string_equal_entail_wit_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hi_lt_na : i < na).
  {
    assert (Hi_lt_la : i < Zlength la).
    {
      apply app_Znth_nonzero_lt with (l := la).
      - rewrite Hlen_la. exact H5.
      - exact H2.
    }
    lia.
  }
  assert (Hi_lt_nb : i < nb).
  {
    assert (Hi_lt_lb : i < Zlength lb).
    {
      apply app_Znth_nonzero_lt with (l := lb).
      - rewrite Hlen_lb. exact H6.
      - exact H0.
    }
    lia.
  }
  entailer!.
  intros j Hj.
  assert (Hcases : j < i \/ j = i) by lia.
  destruct Hcases as [Hj_lt | Hj_eq].
  - apply H9. lia.
  - subst j.
    assert (Hi_range_la : 0 <= i < Zlength la).
    { rewrite Hlen_la. lia. }
    assert (Hi_range_lb : 0 <= i < Zlength lb).
    { rewrite Hlen_lb. lia. }
    rewrite app_Znth1 in H.
    2: exact Hi_range_la.
    rewrite app_Znth1 in H.
    2: exact Hi_range_lb.
    exact H.
Qed.

Lemma proof_of_string_equal_entail_wit_3_1 : string_equal_entail_wit_3_1.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hi_eq_na : i = na).
  {
    eapply first_zero_at_end; eauto.
  }
  subst i.
  left.
  entailer!.
  simpl.
  repeat split; auto; try lia.
  assert (Hheap :
    CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)) **
    (CharArray.full a_pre (na + 1) (app la (cons 0 nil)) **
     ((( &( "i" )) # Int |-> na)))
    |-- ((( &( "i" )) # Int |-> na) **
        (CharArray.full a_pre (na + 1) (app la (cons 0 nil)) **
         CharArray.full b_pre (nb + 1) (app lb (cons 0 nil))))).
  {
    rewrite (logic_equiv_sepcon_assoc
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)))
               (CharArray.full a_pre (na + 1) (app la (cons 0 nil)))
               ((( &( "i" )) # Int |-> na))).
    rewrite (logic_equiv_sepcon_comm
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)) **
                CharArray.full a_pre (na + 1) (app la (cons 0 nil)))
               ((( &( "i" )) # Int |-> na))).
    rewrite (logic_equiv_sepcon_comm
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)))
               (CharArray.full a_pre (na + 1) (app la (cons 0 nil)))).
    entailer!.
  }
  exact (Hheap _ H15).
Qed.

Lemma proof_of_string_equal_entail_wit_3_2 : string_equal_entail_wit_3_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hi_eq_nb : i = nb).
  {
    eapply first_zero_at_end; eauto.
  }
  subst i.
  right.
  entailer!.
  simpl.
  repeat split; auto; try lia.
  assert (Hheap :
    CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)) **
    (CharArray.full a_pre (na + 1) (app la (cons 0 nil)) **
     ((( &( "i" )) # Int |-> nb)))
    |-- ((( &( "i" )) # Int |-> nb) **
        (CharArray.full a_pre (na + 1) (app la (cons 0 nil)) **
         CharArray.full b_pre (nb + 1) (app lb (cons 0 nil))))).
  {
    rewrite (logic_equiv_sepcon_assoc
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)))
               (CharArray.full a_pre (na + 1) (app la (cons 0 nil)))
               ((( &( "i" )) # Int |-> nb))).
    rewrite (logic_equiv_sepcon_comm
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)) **
                CharArray.full a_pre (na + 1) (app la (cons 0 nil)))
               ((( &( "i" )) # Int |-> nb))).
    rewrite (logic_equiv_sepcon_comm
               (CharArray.full b_pre (nb + 1) (app lb (cons 0 nil)))
               (CharArray.full a_pre (na + 1) (app la (cons 0 nil)))).
    entailer!.
  }
  exact (Hheap _ H17).
Qed.

Lemma proof_of_string_equal_entail_wit_4_1 : string_equal_entail_wit_4_1.
Proof.
  pre_process.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hnb_eq_na : nb = na).
  {
    symmetry.
    eapply first_zero_at_end.
    - exact Hlen_lb.
    - intros k Hk0 Hklt.
      apply H7.
      lia.
    - exact H3.
    - exact H5.
    - exact H.
  }
  subst nb.
  rewrite <- Hnb_eq_na.
  entailer!; intros x Hx; rewrite Hnb_eq_na in Hx; first [apply H8 | apply H6]; exact Hx.
Qed.

Lemma proof_of_string_equal_entail_wit_4_2 : string_equal_entail_wit_4_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hna_eq_nb : na = nb).
  {
    symmetry.
    eapply first_zero_at_end.
    - exact Hlen_la.
    - intros k Hk0 Hklt.
      apply H6.
      lia.
    - exact H3.
    - exact H4.
    - exact H1.
  }
  subst na.
  entailer!.
Qed.

Lemma proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  assert (Hi_lt_la : i < Zlength la).
  {
    eapply app_Znth_nonzero_lt.
    - rewrite Hlen_la.
      match goal with
      | H : i <= na |- _ => exact H
      end.
    - match goal with
      | H : Znth i (la ++ 0 :: nil) 0 <> 0 |- _ => exact H
      end.
  }
  assert (Hi_lt_lb : i < Zlength lb).
  {
    eapply app_Znth_nonzero_lt.
    - rewrite Hlen_lb.
      match goal with
      | H : i <= nb |- _ => exact H
      end.
    - match goal with
      | H : Znth i (lb ++ 0 :: nil) 0 <> 0 |- _ => exact H
      end.
  }
  assert (Hspec : string_equal_spec la lb = 0).
  {
    eapply string_equal_spec_mismatch.
    - match goal with
      | H : 0 <= i |- _ => exact H
      end.
    - exact Hi_lt_la.
    - exact Hi_lt_lb.
    - intro Heq.
      apply H.
      assert (Hi_range_la : 0 <= i < Zlength la).
      {
        split.
        - match goal with
          | H : 0 <= i |- _ => exact H
          end.
        - exact Hi_lt_la.
      }
      assert (Hi_range_lb : 0 <= i < Zlength lb).
      {
        split.
        - match goal with
          | H : 0 <= i |- _ => exact H
          end.
        - exact Hi_lt_lb.
      }
      rewrite app_Znth1 by exact Hi_range_la.
      rewrite app_Znth1 by exact Hi_range_lb.
      exact Heq.
    - intros j Hj0 Hjlt.
      match goal with
      | H : forall j : Z, 0 <= j < i -> _ = _ |- _ =>
          apply H; lia
      end.
  }
  rewrite Hspec.
  reflexivity.
Qed.

Lemma proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  assert (Hspec : string_equal_spec la lb = 1).
  {
    eapply string_equal_spec_equal.
    - rewrite Hlen_la, Hlen_lb.
      lia.
    - intros j Hj0 Hjlt.
      rewrite Hlen_la in Hjlt.
      rewrite <- H in Hjlt.
      exact (H2 j (conj Hj0 Hjlt)).
  }
  rewrite Hspec.
  reflexivity.
Qed.

Lemma proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  assert (Hspec : string_equal_spec la lb = 0).
  {
    eapply string_equal_spec_zero_nonzero.
    - exact H3.
    - rewrite Hlen_la.
      exact H4.
    - rewrite Hlen_lb.
      exact H5.
    - exact H1.
    - exact H.
    - intros j Hj0 Hjlt.
      apply H8.
      lia.
  }
  rewrite Hspec.
  reflexivity.
Qed.

Lemma proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  assert (Hspec : string_equal_spec la lb = 0).
  {
    eapply string_equal_spec_zero_nonzero.
    - exact H3.
    - rewrite Hlen_la.
      exact H4.
    - rewrite Hlen_lb.
      exact H5.
    - exact H1.
    - exact H.
    - intros j Hj0 Hjlt.
      apply H8; lia.
  }
  rewrite Hspec.
  reflexivity.
Qed.

Lemma proof_of_string_equal_return_wit_5 : string_equal_return_wit_5.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  rewrite <- Hlen_la in H.
  rewrite Znth_app_zero in H.
  contradiction.
Qed.

Lemma proof_of_string_equal_return_wit_6 : string_equal_return_wit_6.
Proof.
  pre_process.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (la ++ 0 :: nil)) = na + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (lb ++ 0 :: nil)) = nb + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  assert (Hspec : string_equal_spec lb la = 0).
  {
    eapply string_equal_spec_zero_nonzero.
    - exact H1.
    - rewrite Hlen_lb.
      exact H3.
    - rewrite Hlen_la.
      exact H2.
    - rewrite <- Hlen_lb.
      apply Znth_app_zero.
    - exact H.
    - intros j Hj0 Hjlt.
      symmetry.
      apply H6; lia.
  }
  rewrite string_equal_spec_sym.
  rewrite Hspec.
  reflexivity.
Qed.
