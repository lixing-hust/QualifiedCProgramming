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
From SimpleC.EE.CAV.verify_20260422_005007_array_intersection_count_sorted Require Import array_intersection_count_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_intersection_count_sorted.
Local Open Scope sac.

Lemma array_intersection_count_sorted_sublist_head :
  forall (l : list Z) i n,
    0 <= i < n ->
    n <= Zlength l ->
    sublist i n l = Znth i l 0 :: sublist (i + 1) n l.
Proof.
  intros l i n Hi Hn.
  rewrite (sublist_split i n (i + 1) l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  reflexivity.
Qed.

Lemma array_intersection_count_sorted_spec_nil_r :
  forall a, array_intersection_count_sorted_spec a nil = 0.
Proof.
  intros a.
  induction a; simpl; auto.
Qed.

Lemma array_intersection_count_sorted_spec_advance_eq :
  forall la lb i j n m,
    0 <= i < n ->
    0 <= j < m ->
    n <= Zlength la ->
    m <= Zlength lb ->
    Znth i la 0 = Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      1 + array_intersection_count_sorted_spec (sublist (i + 1) n la) (sublist (j + 1) m lb).
Proof.
  intros la lb i j n m Hi Hj Hn Hm Heq.
  rewrite (array_intersection_count_sorted_sublist_head la i n) by lia.
  rewrite (array_intersection_count_sorted_sublist_head lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)); lia.
Qed.

Lemma array_intersection_count_sorted_spec_advance_lt :
  forall la lb i j n m,
    0 <= i < n ->
    0 <= j < m ->
    n <= Zlength la ->
    m <= Zlength lb ->
    Znth i la 0 < Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      array_intersection_count_sorted_spec (sublist (i + 1) n la) (sublist j m lb).
Proof.
  intros la lb i j n m Hi Hj Hn Hm Hlt.
  rewrite (array_intersection_count_sorted_sublist_head la i n) by lia.
  rewrite (array_intersection_count_sorted_sublist_head lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)).
  - lia.
  - idtac.
  destruct (Z.ltb_spec (Znth i la 0) (Znth j lb 0)); lia.
Qed.

Lemma array_intersection_count_sorted_spec_advance_gt :
  forall la lb i j n m,
    0 <= i < n ->
    0 <= j < m ->
    n <= Zlength la ->
    m <= Zlength lb ->
    Znth i la 0 > Znth j lb 0 ->
    array_intersection_count_sorted_spec (sublist i n la) (sublist j m lb) =
      array_intersection_count_sorted_spec (sublist i n la) (sublist (j + 1) m lb).
Proof.
  intros la lb i j n m Hi Hj Hn Hm Hgt.
  rewrite (array_intersection_count_sorted_sublist_head la i n) by lia.
  rewrite (array_intersection_count_sorted_sublist_head lb j m) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)).
  - lia.
  - idtac.
  destruct (Z.ltb_spec (Znth i la 0) (Znth j lb 0)); lia.
Qed.

Lemma proof_of_array_intersection_count_sorted_entail_wit_1 : array_intersection_count_sorted_entail_wit_1.
Proof.
  pre_process.
  rewrite sublist_self by lia.
  rewrite sublist_self by lia.
  entailer!.
Qed.

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_1 : array_intersection_count_sorted_entail_wit_2_1.
Proof.
  pre_process.
  rewrite (array_intersection_count_sorted_spec_advance_gt la lb i_3 j_3 n_pre m_pre) in *
    by lia.
  entailer!.
Qed.

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_2 : array_intersection_count_sorted_entail_wit_2_2.
Proof.
  pre_process.
  rewrite (array_intersection_count_sorted_spec_advance_lt la lb i_3 j_3 n_pre m_pre) in *
    by lia.
  entailer!.
Qed.

Lemma proof_of_array_intersection_count_sorted_entail_wit_2_3 : array_intersection_count_sorted_entail_wit_2_3.
Proof.
  pre_process.
  rewrite (array_intersection_count_sorted_spec_advance_eq la lb i_3 j_3 n_pre m_pre) in *
    by lia.
  entailer!.
Qed.

Lemma proof_of_array_intersection_count_sorted_return_wit_1 : array_intersection_count_sorted_return_wit_1.
Proof.
  pre_process.
  match goal with
  | Hspec: context [array_intersection_count_sorted_spec _ (sublist ?j ?m lb)] |- _ =>
      rewrite (sublist_nil lb j m) in Hspec by lia;
      rewrite array_intersection_count_sorted_spec_nil_r in Hspec;
      assert (count = array_intersection_count_sorted_spec la lb) by lia
  end.
  entailer!.
Qed.

Lemma proof_of_array_intersection_count_sorted_return_wit_2 : array_intersection_count_sorted_return_wit_2.
Proof.
  pre_process.
  match goal with
  | Hspec: context [array_intersection_count_sorted_spec (sublist ?i ?n la) _] |- _ =>
      rewrite (sublist_nil la i n) in Hspec by lia;
      simpl in Hspec;
      assert (count = array_intersection_count_sorted_spec la lb) by lia
  end.
  entailer!.
Qed.
