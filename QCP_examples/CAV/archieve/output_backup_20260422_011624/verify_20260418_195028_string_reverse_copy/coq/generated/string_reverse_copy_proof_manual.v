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
From SimpleC.EE.CAV.verify_20260418_195028_string_reverse_copy Require Import string_reverse_copy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma Znth_rev_Z :
  forall (l : list Z) (k : Z),
    0 <= k < Zlength l ->
    Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0.
Proof.
  intros l k Hk.
  unfold Znth.
  rewrite Zlength_correct.
  rewrite Zlength_correct in Hk.
  rewrite rev_nth by lia.
  replace (length l - S (Z.to_nat k))%nat with (Z.to_nat (Z.of_nat (Datatypes.length l) - 1 - k)) by lia.
  reflexivity.
Qed.

Lemma proof_of_string_reverse_copy_entail_wit_1 : string_reverse_copy_entail_wit_1.
Proof.
  pre_process.
  Exists d nil.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n_pre + 1) d)).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n_pre + 1) d)
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))).
  entailer!.
  rewrite Zlength_correct.
  lia.
Qed.

Lemma proof_of_string_reverse_copy_entail_wit_2 : string_reverse_copy_entail_wit_2.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n_pre + 1)
                (replace_Znth i (Znth (n_pre - 1 - i) (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n_pre + 1)
                (replace_Znth i (Znth (n_pre - 1 - i) (l ++ 0 :: nil) 0) (l1_2 ++ d1_2)))).
  assert (Hlen_l : Zlength l = n_pre).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n_pre + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  destruct d1_2 eqn:Hd1.
  - rewrite Zlength_nil in H4. lia.
  - simpl in H4.
  assert (Hdst :
    replace_Znth i (Znth (n_pre - 1 - i) (l ++ 0 :: nil) 0) (l1_2 ++ z :: l0) =
    (l1_2 ++ cons (Znth (n_pre - 1 - i) l 0) nil) ++ l0).
  {
    rewrite app_Znth1 by lia.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (i - Zlength l1_2) with 0 by lia.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  Exists l0 (l1_2 ++ cons (Znth (n_pre - 1 - i) l 0) nil).
  rewrite Hdst.
  entailer!;
  [ intros k Hk;
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
    [ rewrite app_Znth1 by lia;
      apply H5;
      lia
    | assert (k = i) by lia;
      subst k;
      rewrite app_Znth2 by lia;
      replace (i - Zlength l1_2) with 0 by lia;
      rewrite Znth0_cons;
      reflexivity ]
  | rewrite Zlength_cons in H4; lia
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].
Qed.

Lemma proof_of_string_reverse_copy_return_wit_1 : string_reverse_copy_return_wit_1.
Proof.
  pre_process.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full dst_pre (n_pre + 1) (replace_Znth n_pre 0 (l1 ++ d1)))
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))).
  prop_apply CharArray.full_length. Intros.
  rewrite (logic_equiv_sepcon_comm
             (CharArray.full src_pre (n_pre + 1) (l ++ 0 :: nil))
             (CharArray.full dst_pre (n_pre + 1) (replace_Znth n_pre 0 (l1 ++ d1)))).
  assert (Hlen_l : Zlength l = n_pre).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n_pre + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_eq_n : i = n_pre) by lia.
  subst i.
  assert (Hl1_eq_rev : l1 = rev l).
  {
    apply (proj2 (list_eq_ext 0 l1 (rev l))).
    split.
    - assert (Hlen_l1_now : Zlength l1 = n_pre) by lia.
      assert (Hlen_rev : Zlength (rev l) = n_pre).
      {
        repeat rewrite Zlength_correct.
        rewrite length_rev.
        rewrite <- Zlength_correct.
        exact Hlen_l.
      }
      rewrite Hlen_l1_now.
      symmetry.
      exact Hlen_rev.
    - intros k Hk.
      rewrite Hi_eq_n in Hk.
      rewrite Znth_rev_Z by (rewrite Hlen_l; exact Hk).
      rewrite Hlen_l.
      apply H5.
      lia.
  }
  subst l1.
  assert (Hd1_single : exists x, d1 = x :: nil).
  {
    destruct d1.
    - rewrite Zlength_nil in H4. lia.
    - rewrite Zlength_cons in H4.
      destruct d1.
      + eexists. reflexivity.
      + repeat rewrite Zlength_cons in H4.
        pose proof Zlength_nonneg d1.
        lia.
  }
  destruct Hd1_single.
  subst d1.
  assert (Hlen_l_nat : Z.of_nat (Datatypes.length l) = n_pre).
  {
    rewrite <- Zlength_correct.
    exact Hlen_l.
  }
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (n_pre - Zlength (rev l)) with 0 by lia.
  unfold replace_Znth.
  replace (Z.to_nat (n_pre - Zlength (rev l))) with 0%nat by lia.
  simpl.
  entailer!.
Qed.
