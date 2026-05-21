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
From SimpleC.EE Require Import C_27_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_27.
Local Open Scope sac.

Ltac flip_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simplify_flip :=
  unfold flip_char_z;
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
  simpl.

Ltac rewrite_signed_char :=
  repeat match goal with
  | |- context[signed_last_nbits ?x 8] =>
      rewrite (signed_last_nbits_eq x 8) by lia
  end.

Ltac solve_step_value :=
  intros k Hk;
  match goal with
  | Hlen : Zlength ?ol = ?i,
    Hprefix : forall k : Z, _ -> Znth k ?ol 0 = flip_char_z (Znth k ?l 0) |- _ =>
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix;
        lia
      | assert (k = i) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (i - Zlength ol) with 0 by lia;
        rewrite Znth0_cons;
        repeat rewrite app_Znth1 in * by lia;
        repeat match goal with
        | Hrange : char_range_z ?l |- context[signed_last_nbits (Znth ?idx ?l 0) 8] =>
            let Hr := fresh "Hchar" in
            pose proof (Hrange idx ltac:(lia)) as Hr;
            rewrite (signed_last_nbits_eq (Znth idx l 0) 8) by lia
        end;
        unfold flip_char_z;
        repeat match goal with
        | |- context[Z.leb ?x ?y] =>
            destruct (Z.leb_spec x y); simpl
        end;
        lia ]
  end.

Ltac solve_step :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | |- context[CharArray.full ?out (?i + 1) (app ?ol (cons ?v nil))] =>
      Exists (app ol (cons v nil))
  end;
  entailer!;
  [ solve_step_value
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_filp_case_entail_wit_1 : filp_case_entail_wit_1.
Proof.
  unfold filp_case_entail_wit_1.
  intros.
  flip_pre.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_filp_case_entail_wit_2_1 : filp_case_entail_wit_2_1.
Proof.
  unfold filp_case_entail_wit_2_1.
  intros.
  solve_step.
Qed. 

Lemma proof_of_filp_case_entail_wit_2_2 : filp_case_entail_wit_2_2.
Proof.
  unfold filp_case_entail_wit_2_2.
  intros.
  solve_step.
Qed. 

Lemma proof_of_filp_case_entail_wit_2_3 : filp_case_entail_wit_2_3.
Proof.
  unfold filp_case_entail_wit_2_3.
  intros.
  solve_step.
Qed. 

Lemma proof_of_filp_case_entail_wit_2_4 : filp_case_entail_wit_2_4.
Proof.
  unfold filp_case_entail_wit_2_4.
  intros.
  solve_step.
Qed. 

Lemma proof_of_filp_case_entail_wit_2_5 : filp_case_entail_wit_2_5.
Proof.
  unfold filp_case_entail_wit_2_5.
  intros.
  solve_step.
Qed. 

Lemma proof_of_filp_case_return_wit_1 : filp_case_return_wit_1.
Proof.
  unfold filp_case_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  match goal with
  | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
  end.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - apply problem_27_spec_z_intro with (n := len); try lia; try assumption.
    intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char_z (Znth k l 0) |- _ =>
        apply Hprefix; lia
    end.
Qed. 
