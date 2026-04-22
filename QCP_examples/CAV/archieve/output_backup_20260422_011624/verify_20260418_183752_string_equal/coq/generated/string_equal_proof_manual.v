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
From SimpleC.EE.CAV.verify_20260418_183752_string_equal Require Import string_equal_goal.
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
  unfold string_equal_entail_wit_2.
  intros b_pre a_pre nb na lb la i Heq Hib_nz Hna1 Hia_nz Hnb1 Hi0 Hina Hinb Hla_nz1 Hlb_nz1 Hpref Hna0 HnaMax Hnb0 HnbMax Hla_nz Hlb_nz.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hi_lt_na : i < na).
  {
    rewrite <- Hlen_la.
    eapply app_Znth_nonzero_lt; eauto.
  }
  assert (Hi_lt_nb : i < nb).
  {
    rewrite <- Hlen_lb.
    eapply app_Znth_nonzero_lt; eauto.
  }
  entailer!.
  intros j Hj0 Hjlt.
  assert (Hcases : j < i \/ j = i) by lia.
  destruct Hcases as [Hlt | Heqj].
  - apply Hpref; lia.
  - subst j.
    rewrite app_Znth1 in Heq by (rewrite Hlen_la; lia).
    rewrite app_Znth1 in Heq by (rewrite Hlen_lb; lia).
    exact Heq.
Qed.

Lemma proof_of_string_equal_entail_wit_3_1 : string_equal_entail_wit_3_1.
Proof.
  unfold string_equal_entail_wit_3_1.
  intros b_pre a_pre nb na lb la i Hzero Hnb1 Hi0 Hina Hinb Hla_nz1 Hlb_nz1 Hpref Hna0 HnaMax Hnb0 HnbMax Hla_nz Hlb_nz.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
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
  intros j Hj0 Hjlt.
  apply Hpref; lia.
Qed.

Lemma proof_of_string_equal_entail_wit_3_2 : string_equal_entail_wit_3_2.
Proof.
  unfold string_equal_entail_wit_3_2.
  intros b_pre a_pre nb na lb la i Hzero Hna1 Hia_nz Hnb1 Hi0 Hina Hinb Hla_nz1 Hlb_nz1 Hpref Hna0 HnaMax Hnb0 HnbMax Hla_nz Hlb_nz.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
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
  intros j Hj0 Hjlt.
  apply Hpref; lia.
Qed.

Lemma proof_of_string_equal_entail_wit_4_1 : string_equal_entail_wit_4_1.
Proof.
  unfold string_equal_entail_wit_4_1.
  intros b_pre a_pre nb na lb la Hlb_zero Hna1 Hla_zero Hnb1 Hna0 Hna_le Hna_nb Hla_nz Hlb_nz Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hnb_eq_na : nb = na).
  {
    symmetry.
    eapply first_zero_at_end; eauto.
  }
  subst nb.
  entailer!.
Qed.

Lemma proof_of_string_equal_entail_wit_4_2 : string_equal_entail_wit_4_2.
Proof.
  unfold string_equal_entail_wit_4_2.
  intros b_pre a_pre nb na lb la Hlb_zero Hna1 Hla_zero Hnb1 Hnb0 Hnb_na Hnb_le Hla_nz Hlb_nz Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hnb_eq_na : nb = na).
  {
    eapply first_zero_at_end; eauto.
  }
  subst na.
  entailer!.
Qed.

Lemma proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Proof.
  unfold string_equal_return_wit_1.
  intros b_pre a_pre nb na lb la i Hneq Hib_nz Hna1 Hia_nz Hnb1 Hi0 Hina Hinb Hla_nz Hlb_nz Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hi_lt_na : i < na).
  {
    rewrite <- Hlen_la.
    eapply app_Znth_nonzero_lt; eauto.
  }
  assert (Hi_lt_nb : i < nb).
  {
    rewrite <- Hlen_lb.
    eapply app_Znth_nonzero_lt; eauto.
  }
  rewrite app_Znth1 in Hneq by (rewrite Hlen_la; lia).
  rewrite app_Znth1 in Hneq by (rewrite Hlen_lb; lia).
  entailer!.
  symmetry.
  eapply string_equal_spec_mismatch.
  - exact Hi0.
  - rewrite Hlen_la. exact Hi_lt_na.
  - rewrite Hlen_lb. exact Hi_lt_nb.
  - exact Hneq.
  - exact Hpref.
Qed.

Lemma proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Proof.
  unfold string_equal_return_wit_2.
  intros b_pre a_pre nb na lb la Hlen_eq Hla_nz Hlb_nz Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  symmetry.
  eapply string_equal_spec_equal.
  - rewrite Hlen_la, Hlen_lb, Hlen_eq. reflexivity.
  - intros j Hj0 Hjlt.
    apply Hpref; lia.
Qed.

Lemma proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Proof.
  unfold string_equal_return_wit_3.
  intros b_pre a_pre nb na lb la Hlb_nz Hna1 Hla_zero Hnb1 Hnb0 Hnb_na Hnb_le Hla_nz Hlb_nz_all Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  symmetry.
  eapply string_equal_spec_zero_nonzero.
  - exact Hnb0.
  - rewrite Hlen_la. exact Hnb_na.
  - rewrite Hlen_lb. exact Hnb_le.
  - exact Hla_zero.
  - exact Hlb_nz.
  - exact Hpref.
Qed.

Lemma proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
Proof.
  unfold string_equal_return_wit_4.
  intros b_pre a_pre nb na lb la Hlb_nz Hna1 Hla_zero Hnb1 Hna0 Hna_le Hna_nb Hla_nz Hlb_nz_all Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  entailer!.
  symmetry.
  eapply string_equal_spec_zero_nonzero.
  - exact Hna0.
  - rewrite Hlen_la. exact Hna_le.
  - rewrite Hlen_lb. exact Hna_nb.
  - exact Hla_zero.
  - exact Hlb_nz.
  - exact Hpref.
Qed.

Lemma proof_of_string_equal_return_wit_5 : string_equal_return_wit_5.
Proof.
  unfold string_equal_return_wit_5.
  intros b_pre a_pre nb na lb la Hla_nz Hnb1 Hna0 Hna_le Hna_nb Hpref.
  Intros.
  prop_apply (CharArray.full_length a_pre (na + 1) (app la (cons 0 nil))). Intros.
  assert (Hlen_la : Zlength la = na).
  {
    match goal with
    | Hlen : Zlength (app la (cons 0 nil)) = na + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  rewrite <- Hlen_la in Hla_nz.
  rewrite Znth_app_zero in Hla_nz.
  contradiction.
Qed.

Lemma proof_of_string_equal_return_wit_6 : string_equal_return_wit_6.
Proof.
  unfold string_equal_return_wit_6.
  intros b_pre a_pre nb na lb la Hla_nz Hnb1 Hnb0 Hnb_na Hnb_le Hpref.
  Intros.
  prop_apply (CharArray.full_length b_pre (nb + 1) (app lb (cons 0 nil))). Intros.
  assert (Hlen_lb : Zlength lb = nb).
  {
    match goal with
    | Hlen : Zlength (app lb (cons 0 nil)) = nb + 1 |- _ =>
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen; lia
    end.
  }
  rewrite <- Hlen_lb in Hla_nz.
  rewrite Znth_app_zero in Hla_nz.
  contradiction.
Qed.
