Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_144_goal.
From SimpleC.EE Require Import C_144_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_144.
Local Open Scope sac.

Lemma proof_of_simplify_safety_wit_17 : simplify_safety_wit_17.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 lx i PreH18 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_18 : simplify_safety_wit_18.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 lx i PreH18 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_22 : simplify_safety_wit_22.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 lx i PreH18 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_23 : simplify_safety_wit_23.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 lx i PreH18 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_38 : simplify_safety_wit_38.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 ln i PreH17 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_39 : simplify_safety_wit_39.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 ln i PreH17 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_43 : simplify_safety_wit_43.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 ln i PreH17 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_44 : simplify_safety_wit_44.
Proof.
  right; intros; entailer!.
  all: pose proof (valid_string_c_string_inside_144 ln i PreH17 ltac:(lia)) as Hchar;
       nia.
Qed.

Lemma proof_of_simplify_safety_wit_50 : simplify_safety_wit_50.
Proof. right; intros; entailer!; nia. Qed.

Lemma proof_of_simplify_safety_wit_51 : simplify_safety_wit_51.
Proof. right; intros; entailer!; nia. Qed.

Lemma proof_of_simplify_safety_wit_52 : simplify_safety_wit_52.
Proof. right; intros; entailer!; nia. Qed.

Lemma proof_of_simplify_entail_wit_1 : simplify_entail_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  apply (fraction_scan_state_144_init lx sx ax bx); exact PreH10.
  subst retval; apply string_length_nonneg.
Qed.

Lemma proof_of_simplify_entail_wit_2_1 : simplify_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length lx) by lia.
  assert (Hil : i < Zlength lx) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH2 |- * by exact Hi.
  subst seen_x.
  pose proof (fraction_scan_state_144_den_step
    lx sx ax bx i a b PreH23 PreH25 Hil PreH2) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    lx sx ax bx (i + 1) 1 a
      (b * 10 + digit_value_z_144 (Znth i lx 0)) PreH23 Hstep) as Hbounds.
  pose proof (valid_string_c_string_inside_144 lx i PreH18 Hi) as Hchar.
  rewrite c_string_Znth_inside in Hchar by exact Hi.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_2_2 : simplify_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length lx) by lia.
  assert (Hil : i < Zlength lx) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH2 |- * by exact Hi.
  subst seen_x.
  pose proof (fraction_scan_state_144_num_step
    lx sx ax bx i a b PreH23 PreH25 Hil PreH2) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    lx sx ax bx (i + 1) 0
      (a * 10 + digit_value_z_144 (Znth i lx 0)) b PreH23 Hstep) as Hbounds.
  pose proof (valid_string_c_string_inside_144 lx i PreH18 Hi) as Hchar.
  rewrite c_string_Znth_inside in Hchar by exact Hi.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_2_3 : simplify_entail_wit_2_3.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length lx) by lia.
  assert (Hil : i < Zlength lx) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH1 |- * by exact Hi.
  pose proof (fraction_scan_state_144_slash_step
    lx sx ax bx i seen_x a b PreH22 PreH24 Hil PreH1) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    lx sx ax bx (i + 1) 1 a b PreH22 Hstep) as Hbounds.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_2_4 : simplify_entail_wit_2_4.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length lx) by lia.
  assert (Hil : i < Zlength lx) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH1 |- * by exact Hi.
  pose proof (fraction_scan_state_144_slash_step
    lx sx ax bx i seen_x a b PreH22 PreH24 Hil PreH1) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    lx sx ax bx (i + 1) 1 a b PreH22 Hstep) as Hbounds.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_4_1 : simplify_entail_wit_4_1.
Proof.
  left; intros.
  assert (Hi : i = Zlength lx) by (unfold string_length in *; lia).
  subst i.
  pose proof (fraction_scan_state_144_finish
    lx sx ax bx seen_x a b PreH21 PreH23) as Hfinish.
  destruct Hfinish as (Hseen & Ha & Hb).
  exfalso; lia.
Qed.

Lemma proof_of_simplify_entail_wit_4_2 : simplify_entail_wit_4_2.
Proof.
  left; intros.
  assert (Hi : i = Zlength lx) by (unfold string_length in *; lia).
  subst i.
  pose proof (fraction_scan_state_144_finish
    lx sx ax bx seen_x a b PreH21 PreH23) as Hfinish.
  destruct Hfinish as (Hseen & Ha & Hb).
  subst a; subst b.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_5 : simplify_entail_wit_5.
Proof.
  pre_process.
  subst c; subst d; subst seen_n.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  - apply (fraction_scan_state_144_init ln sy cn dn); exact PreH16.
  - subst len_n; apply string_length_nonneg.
Qed.

Lemma proof_of_simplify_entail_wit_6_1 : simplify_entail_wit_6_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length ln) by lia.
  assert (Hil : i < Zlength ln) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH2 |- * by exact Hi.
  subst seen_n.
  pose proof (fraction_scan_state_144_den_step
    ln sy cn dn i c d PreH22 PreH23 Hil PreH2) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    ln sy cn dn (i + 1) 1 c
      (d * 10 + digit_value_z_144 (Znth i ln 0)) PreH22 Hstep) as Hbounds.
  pose proof (valid_string_c_string_inside_144 ln i PreH17 Hi) as Hchar.
  rewrite c_string_Znth_inside in Hchar by exact Hi.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_6_2 : simplify_entail_wit_6_2.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length ln) by lia.
  assert (Hil : i < Zlength ln) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH2 |- * by exact Hi.
  subst seen_n.
  pose proof (fraction_scan_state_144_num_step
    ln sy cn dn i c d PreH22 PreH23 Hil PreH2) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    ln sy cn dn (i + 1) 0
      (c * 10 + digit_value_z_144 (Znth i ln 0)) d PreH22 Hstep) as Hbounds.
  pose proof (valid_string_c_string_inside_144 ln i PreH17 Hi) as Hchar.
  rewrite c_string_Znth_inside in Hchar by exact Hi.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_6_3 : simplify_entail_wit_6_3.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length ln) by lia.
  assert (Hil : i < Zlength ln) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH1 |- * by exact Hi.
  pose proof (fraction_scan_state_144_slash_step
    ln sy cn dn i seen_n c d PreH21 PreH22 Hil PreH1) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    ln sy cn dn (i + 1) 1 c d PreH21 Hstep) as Hbounds.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_6_4 : simplify_entail_wit_6_4.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length ln) by lia.
  assert (Hil : i < Zlength ln) by (unfold string_length in *; lia).
  rewrite c_string_Znth_inside in PreH1 |- * by exact Hi.
  pose proof (fraction_scan_state_144_slash_step
    ln sy cn dn i seen_n c d PreH21 PreH22 Hil PreH1) as Hstep.
  pose proof (fraction_scan_state_144_bounds
    ln sy cn dn (i + 1) 1 c d PreH21 Hstep) as Hbounds.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_8_1 : simplify_entail_wit_8_1.
Proof.
  left; intros.
  assert (Hi : i = Zlength ln) by (unfold string_length in *; lia).
  subst i.
  pose proof (fraction_scan_state_144_finish
    ln sy cn dn seen_n c d PreH20 PreH21) as Hfinish.
  destruct Hfinish as (Hseen & Hc & Hd).
  subst c; subst d.
  entailer!.
Qed.

Lemma proof_of_simplify_entail_wit_8_2 : simplify_entail_wit_8_2.
Proof.
  left; intros.
  assert (Hi : i = Zlength ln) by (unfold string_length in *; lia).
  subst i.
  pose proof (fraction_scan_state_144_finish
    ln sy cn dn seen_n c d PreH20 PreH21) as Hfinish.
  destruct Hfinish as (Hseen & Hc & Hd).
  exfalso; lia.
Qed.

Lemma proof_of_simplify_return_wit_1 : simplify_return_wit_1.
Proof.
  right; intros; entailer!.
  eapply problem_144_spec_z_from_parts; [exact PreH16 | exact PreH17 |].
  destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * dn)) 0);
    [contradiction | reflexivity].
Qed.

Lemma proof_of_simplify_return_wit_2 : simplify_return_wit_2.
Proof.
  right; intros; entailer!.
  eapply problem_144_spec_z_from_parts; [exact PreH16 | exact PreH17 |].
  destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * dn)) 0);
    [reflexivity | contradiction].
Qed.
