Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_161_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_161.
Local Open Scope sac.

Ltac prep_161 :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simp_letter_161 :=
  unfold is_letter_zb, is_lower_zb, is_upper_zb, flip_char_z;
  repeat match goal with
  | H : ?x <= ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?y >= ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?x > ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?y < ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  end;
  repeat rewrite Bool.orb_true_r;
  repeat rewrite Bool.orb_true_l;
  repeat rewrite Bool.orb_false_r;
  repeat rewrite Bool.orb_false_l;
  repeat rewrite Bool.andb_false_r;
  repeat rewrite Bool.andb_false_l;
  repeat rewrite Bool.andb_true_r;
  repeat rewrite Bool.andb_true_l;
  simpl.

Ltac rewrite_signed_input_161 :=
  repeat match goal with
  | Hrange : ascii_range_z ?lst |- context[signed_last_nbits (Znth ?idx ?lst 0) 8] =>
      let Hr := fresh "Hchar" in
      pose proof (Hrange idx ltac:(lia)) as Hr;
      rewrite (signed_last_nbits_eq (Znth idx lst 0) 8) by lia
  end.

Ltac choose_app_out_161 :=
  match goal with
  | |- context[CharArray.full _ _ (app ?ol (cons (signed_last_nbits (Znth (Zlength ?ol) ?inp 0) 8) nil))] =>
      Exists (app ol (cons (signed_last_nbits (Znth (Zlength ol) inp 0) 8) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (?n - 1 - Zlength ?ol) ?inp 0) nil))] =>
      Exists (app ol (cons (Znth (n - 1 - Zlength ol) inp 0) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0 - 32) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0 - 32) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0 + 32) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0 + 32) nil))
  end.

Ltac solve_extend_flip_161 :=
  prep_161;
  choose_app_out_161;
  entailer!;
  [ intros k Hk;
    match goal with
    | Hprefix : forall x : Z, 0 <= x < Zlength ?ol -> _ |- _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          apply Hprefix; lia
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite_signed_input_161;
          cbv [flip_char_z is_lower_zb is_upper_zb];
          repeat match goal with
          | |- context[Z.leb ?x ?y] =>
              destruct (Z.leb_spec x y); simpl
          end; try reflexivity; lia ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac finish_extend_flip_161 :=
  entailer!;
  [ intros k Hk;
    match goal with
    | |- Znth k (?ol ++ _) 0 = _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          match goal with Hprefix : forall x : Z, _ -> _ |- _ => apply Hprefix; lia end
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite_signed_input_161;
          cbv [flip_char_z is_lower_zb is_upper_zb];
          repeat match goal with
          | |- context[Z.leb ?x ?y] =>
              destruct (Z.leb_spec x y); simpl
          end; try reflexivity; lia ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac solve_extend_rev_161 :=
  prep_161;
  choose_app_out_161;
  entailer!;
  [ intros k Hk;
    match goal with
    | Hlen : Zlength ?ol = ?i,
      Hprefix : forall x : Z, 0 <= x < Zlength ?ol -> _ |- _ =>
        destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          apply Hprefix; lia
        | assert (k = i) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (i - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite app_Znth1 by lia;
          reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac finish_extend_rev_161 :=
  entailer!;
  [ intros k Hk;
    match goal with
    | |- Znth k (?ol ++ _) 0 = _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          match goal with Hprefix : forall x : Z, _ -> _ |- _ => apply Hprefix; lia end
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          try rewrite app_Znth1 by lia;
          reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  unfold solve_entail_wit_1.
  intros.
  prep_161.
  entailer!.
Qed.

Lemma proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Proof.
  unfold solve_entail_wit_2_1.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_z_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Proof.
  unfold solve_entail_wit_2_2.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_z_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2_3 : solve_entail_wit_2_3.
Proof.
  unfold solve_entail_wit_2_3.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_z_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2_4 : solve_entail_wit_2_4.
Proof.
  unfold solve_entail_wit_2_4.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_z_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_2_5 : solve_entail_wit_2_5.
Proof.
  unfold solve_entail_wit_2_5.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_z_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  unfold solve_entail_wit_3.
  intros.
  prep_161.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg out 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty out 0).
  rewrite (CharArray.full_empty out 0).
  entailer!.
  - rewrite <- contains_letter_prefix_z_full.
    match goal with
    | H : 1 = contains_letter_prefix_z ?idx l |- _ =>
        replace (Zlength l) with idx by lia; exact H
    | H : contains_letter_prefix_z ?idx l = 1 |- _ =>
        replace (Zlength l) with idx by lia; symmetry; exact H
    end.
  - rewrite Zlength_correct; lia.
Qed.

Lemma proof_of_solve_entail_wit_4_1 : solve_entail_wit_4_1.
Proof.
  unfold solve_entail_wit_4_1.
  intros.
  prep_161.
  Exists (out_l_2 ++ signed_last_nbits (Znth (Zlength out_l_2) l 0) 8 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
  Unshelve.
  all: try solve [rewrite Zlength_correct; lia | lia].
Qed.

Lemma proof_of_solve_entail_wit_4_2 : solve_entail_wit_4_2.
Proof.
  unfold solve_entail_wit_4_2.
  intros.
  prep_161.
  Exists (out_l_2 ++ Znth (Zlength out_l_2) l 0 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_solve_entail_wit_4_3 : solve_entail_wit_4_3.
Proof.
  unfold solve_entail_wit_4_3.
  intros.
  prep_161.
  Exists (out_l_2 ++ signed_last_nbits (Znth (Zlength out_l_2) l 0) 8 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_solve_entail_wit_4_4 : solve_entail_wit_4_4.
Proof.
  unfold solve_entail_wit_4_4.
  intros.
  prep_161.
  Exists (out_l_2 ++ (Znth (Zlength out_l_2) l 0 - 32) :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_solve_entail_wit_4_5 : solve_entail_wit_4_5.
Proof.
  unfold solve_entail_wit_4_5.
  intros.
  prep_161.
  Exists (out_l_2 ++ (Znth (Zlength out_l_2) l 0 + 32) :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  unfold solve_entail_wit_5.
  intros.
  prep_161.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg out 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty out 0).
  rewrite (CharArray.full_empty out 0).
  entailer!.
  - try rewrite <- contains_letter_prefix_z_full.
    try match goal with
    | H : 0 = contains_letter_prefix_z ?idx l |- _ =>
        replace (Zlength l) with idx by lia; exact H
    | H : contains_letter_prefix_z ?idx l = 0 |- _ =>
        replace (Zlength l) with idx by lia; symmetry; exact H
    end.
    pose proof (contains_letter_prefix_z_bool i l); lia.
  - destruct (contains_letter_prefix_z_bool i l) as [Hz | Hz]; try lia.
    replace i with (Zlength l) by lia.
    rewrite contains_letter_prefix_z_full.
    reflexivity.
  - rewrite Zlength_correct; lia.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  unfold solve_entail_wit_6.
  intros.
  prep_161.
  Exists (out_l_2 ++ Znth (Zlength l - 1 - Zlength out_l_2) l 0 :: nil).
  finish_extend_rev_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  unfold solve_return_wit_1.
  intros.
  prep_161.
  assert (Hout_len_eq : Zlength out_l_2 = Zlength l) by lia.
  Exists out_l_2.
  replace (Zlength out_l_2 + 1) with (Zlength l + 1) by lia.
  rewrite (CharArray.undef_seg_empty out (Zlength l + 1)).
  entailer!.
  - apply problem_161_spec_z_intro_rev; try assumption.
    + apply output_is_rev_161.
      * assumption.
      * intros k Hk.
        match goal with
        | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = Znth (Zlength l - 1 - k) l 0 |- _ =>
            apply Hprefix; lia
        end.
Qed.

Lemma proof_of_solve_return_wit_2 : solve_return_wit_2.
Proof.
  unfold solve_return_wit_2.
  intros.
  prep_161.
  assert (Hout_len_eq : Zlength out_l_2 = Zlength l) by lia.
  Exists out_l_2.
  replace (Zlength out_l_2 + 1) with (Zlength l + 1) by lia.
  rewrite (CharArray.undef_seg_empty out (Zlength l + 1)).
  entailer!.
  - apply problem_161_spec_z_intro_flip; try assumption.
    + apply output_is_map_flip_161.
      * assumption.
      * intros k Hk.
        match goal with
        | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char_z (Znth k l 0) |- _ =>
            apply Hprefix; lia
        end.
Qed.
