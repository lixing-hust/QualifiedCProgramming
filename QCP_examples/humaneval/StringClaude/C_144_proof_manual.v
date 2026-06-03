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
From SimpleC.EE Require Import C_144_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_144.
Local Open Scope sac.

Ltac open_safe_values_144 :=
  repeat match goal with
  | H : fraction_values_safe_z _ _ _ _ |- _ =>
      unfold fraction_values_safe_z in H;
      destruct H as ((? & ?) & (? & ?) & (? & ?) & (? & ?))
  end.

Ltac add_char_digit_144 :=
  match goal with
  | Hparts : fraction_parts_z ?s ?slash ?num ?den,
    Hneq : Znth ?i (app ?s (cons 0 nil)) 0 <> 47 |- context[Znth ?i (app ?s (cons 0 nil)) 0] =>
      let Hlt := fresh "Hlt" in
      let Hdig := fresh "Hdig" in
      pose proof (fraction_parts_z_num_loop_lt s slash num den i Hparts ltac:(lia) Hneq) as Hlt;
      pose proof (fraction_parts_z_num_digit_app s slash num den i Hparts ltac:(lia)) as Hdig;
      unfold digit_char_z in Hdig
  | Hparts : fraction_parts_z ?s ?slash ?num ?den |- context[Znth ?i (app ?s (cons 0 nil)) 0] =>
      let Hdig := fresh "Hdig" in
      pose proof (fraction_parts_z_den_digit_app s slash num den i Hparts ltac:(lia)) as Hdig;
      unfold digit_char_z in Hdig
  end.

Ltac solve_safety_144 :=
  pre_process;
  subst;
  entailer!;
  open_safe_values_144;
  try add_char_digit_144;
  try nia.

Ltac solve_basic_entail_144 :=
  pre_process;
  subst;
  entailer!;
  try rewrite parse_digits_z_empty;
  open_safe_values_144;
  unfold fraction_parts_z in *;
  try nia.

Ltac solve_num_step_144 :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hparts : fraction_parts_z ?s ?slash ?num ?den,
    Hneq : Znth ?i (app ?s (cons 0 nil)) 0 <> 47 |- _ =>
      let Hlt := fresh "Hlt" in
      let Hstep := fresh "Hstep" in
      let Hbound := fresh "Hbound" in
      pose proof (fraction_parts_z_num_loop_lt s slash num den i Hparts ltac:(lia) Hneq) as Hlt;
      pose proof (fraction_parts_z_num_step_value s slash num den i Hparts ltac:(lia)) as Hstep;
      pose proof (fraction_parts_z_num_step_bound s slash num den i Hparts ltac:(lia)) as Hbound;
      try rewrite Hstep;
      try rewrite <- Hstep;
      lia
  end.

Ltac solve_den_step_144 :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hparts : fraction_parts_z ?s ?slash ?num ?den,
    Hlo : ?slash + 1 <= ?i,
    Hhi : ?i < Zlength ?s |- _ =>
      let Hstep := fresh "Hstep" in
      let Hbound := fresh "Hbound" in
      pose proof (fraction_parts_z_den_step_value s slash num den i Hparts ltac:(lia)) as Hstep;
      pose proof (fraction_parts_z_den_step_bound s slash num den i Hparts ltac:(lia)) as Hbound;
      try rewrite Hstep;
      try rewrite <- Hstep;
      lia
  end.

Lemma proof_of_simplify_safety_wit_7 : simplify_safety_wit_7.
Proof.
  unfold simplify_safety_wit_7.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_8 : simplify_safety_wit_8.
Proof.
  unfold simplify_safety_wit_8.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_9 : simplify_safety_wit_9.
Proof.
  unfold simplify_safety_wit_9.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_15 : simplify_safety_wit_15.
Proof.
  unfold simplify_safety_wit_15.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_16 : simplify_safety_wit_16.
Proof.
  unfold simplify_safety_wit_16.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_17 : simplify_safety_wit_17.
Proof.
  unfold simplify_safety_wit_17.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_23 : simplify_safety_wit_23.
Proof.
  unfold simplify_safety_wit_23.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_24 : simplify_safety_wit_24.
Proof.
  unfold simplify_safety_wit_24.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_25 : simplify_safety_wit_25.
Proof.
  unfold simplify_safety_wit_25.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_31 : simplify_safety_wit_31.
Proof.
  unfold simplify_safety_wit_31.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_32 : simplify_safety_wit_32.
Proof.
  unfold simplify_safety_wit_32.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_33 : simplify_safety_wit_33.
Proof.
  unfold simplify_safety_wit_33.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_37 : simplify_safety_wit_37.
Proof.
  unfold simplify_safety_wit_37.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_38 : simplify_safety_wit_38.
Proof.
  unfold simplify_safety_wit_38.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_simplify_safety_wit_39 : simplify_safety_wit_39.
Proof.
  unfold simplify_safety_wit_39.
  intros.
  pre_process.
  subst.
  entailer!;
  open_safe_values_144;
  match goal with
  | Hparts : fraction_parts_z ?s ?slash ?num ?den |- context[parse_digits_z (sublist (?slash + 1) ?i ?s)] =>
      assert (parse_digits_z (sublist (slash + 1) i s) = den) by
        (assert (i = Zlength s) by lia;
         subst i;
         symmetry;
         eapply fraction_parts_z_den_value; eauto)
  end;
  nia.
Qed. 

Lemma proof_of_simplify_entail_wit_1 : simplify_entail_wit_1.
Proof.
  unfold simplify_entail_wit_1.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_simplify_entail_wit_2 : simplify_entail_wit_2.
Proof.
  unfold simplify_entail_wit_2.
  intros.
  solve_num_step_144.
Qed. 

Lemma proof_of_simplify_entail_wit_3 : simplify_entail_wit_3.
Proof.
  unfold simplify_entail_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = sx) by (eapply fraction_parts_z_slash_index; eauto; lia).
  subst i.
  assert (Hax : parse_digits_z (sublist 0 sx lx) = ax) by
    (symmetry; eapply fraction_parts_z_num_value; eauto).
  rewrite Hax.
  entailer!.
Qed. 

Lemma proof_of_simplify_entail_wit_4 : simplify_entail_wit_4.
Proof.
  unfold simplify_entail_wit_4.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_simplify_entail_wit_5 : simplify_entail_wit_5.
Proof.
  unfold simplify_entail_wit_5.
  intros.
  solve_den_step_144.
Qed. 

Lemma proof_of_simplify_entail_wit_6 : simplify_entail_wit_6.
Proof.
  unfold simplify_entail_wit_6.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength lx) by lia.
  subst i.
  assert (Hbx : parse_digits_z (sublist (sx + 1) (Zlength lx) lx) = bx) by
    (symmetry; eapply fraction_parts_z_den_value; eauto).
  rewrite Hbx.
  entailer!.
Qed. 

Lemma proof_of_simplify_entail_wit_8 : simplify_entail_wit_8.
Proof.
  unfold simplify_entail_wit_8.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_simplify_entail_wit_9 : simplify_entail_wit_9.
Proof.
  unfold simplify_entail_wit_9.
  intros.
  solve_num_step_144.
Qed. 

Lemma proof_of_simplify_entail_wit_10 : simplify_entail_wit_10.
Proof.
  unfold simplify_entail_wit_10.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = sn) by (eapply fraction_parts_z_slash_index; eauto; lia).
  subst i.
  assert (Hcn : parse_digits_z (sublist 0 sn ln) = cn) by
    (symmetry; eapply fraction_parts_z_num_value; eauto).
  rewrite Hcn.
  entailer!.
Qed. 

Lemma proof_of_simplify_entail_wit_11 : simplify_entail_wit_11.
Proof.
  unfold simplify_entail_wit_11.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_simplify_entail_wit_12 : simplify_entail_wit_12.
Proof.
  unfold simplify_entail_wit_12.
  intros.
  solve_den_step_144.
Qed. 

Lemma proof_of_simplify_return_wit_1 : simplify_return_wit_1.
Proof.
  unfold simplify_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (Hdn : parse_digits_z (sublist (sn + 1) i ln) = dn) by
    (assert (i = Zlength ln) by lia;
     subst i;
     symmetry;
     eapply fraction_parts_z_den_value; eauto).
  apply problem_144_spec_z_intro with (sx := sx) (sn := sn) (a := ax) (b := bx) (c := cn) (d := dn).
  - exact H6.
  - exact H7.
  - exact H8.
  - rewrite <- Hdn.
    destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * parse_digits_z (sublist (sn + 1) i ln))) 0).
    + exfalso. apply H. exact e.
    + reflexivity.
Qed. 

Lemma proof_of_simplify_return_wit_2 : simplify_return_wit_2.
Proof.
  unfold simplify_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (Hdn : parse_digits_z (sublist (sn + 1) i ln) = dn) by
    (assert (i = Zlength ln) by lia;
     subst i;
     symmetry;
     eapply fraction_parts_z_den_value; eauto).
  apply problem_144_spec_z_intro with (sx := sx) (sn := sn) (a := ax) (b := bx) (c := cn) (d := dn).
  - exact H6.
  - exact H7.
  - exact H8.
  - rewrite <- Hdn.
    destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * parse_digits_z (sublist (sn + 1) i ln))) 0).
    + reflexivity.
    + contradiction.
Qed. 
