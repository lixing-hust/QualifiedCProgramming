Load "../spec/93".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_upper_z (c : Z) : Prop := 65 <= c <= 90.
Definition is_lower_z (c : Z) : Prop := 97 <= c <= 122.
Definition is_space_z (c : Z) : Prop := c = 32.

Definition problem_93_pre_z (s : list Z) : Prop :=
  problem_93_pre (string_of_list_z s).

Definition swap_case_z (c : Z) : Z :=
  if andb (Z.leb 97 c) (Z.leb c 122) then c - 32
  else if andb (Z.leb 65 c) (Z.leb c 90) then c + 32
  else c.

Definition is_vowel_z (c : Z) : bool :=
  orb (Z.eqb c 65)
  (orb (Z.eqb c 69)
  (orb (Z.eqb c 73)
  (orb (Z.eqb c 79)
  (orb (Z.eqb c 85)
  (orb (Z.eqb c 97)
  (orb (Z.eqb c 101)
  (orb (Z.eqb c 105)
  (orb (Z.eqb c 111) (Z.eqb c 117))))))))).

Definition encode_char_z (c : Z) : Z :=
  let w := swap_case_z c in
  if is_vowel_z w then w + 2 else w.

Definition problem_93_spec_z (input output : list Z) : Prop :=
  problem_93_spec (string_of_list_z input) (string_of_list_z output).

Lemma problem_93_pre_z_char : forall s k,
  problem_93_pre_z s ->
  ascii_range_z s ->
  0 <= k < Zlength s ->
  is_upper_z (Znth k s 0) \/ is_lower_z (Znth k s 0) \/ is_space_z (Znth k s 0).
Proof.
  intros s k Hpre Hrange Hk.
  unfold problem_93_pre_z, problem_93_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  apply Forall_forall with (x := ascii_of_z (Znth k s 0)) in Hpre.
  - unfold is_upper_z, is_lower_z, is_space_z, ascii_range_z in *.
    rewrite nat_of_ascii_ascii_of_z in Hpre by (apply Hrange; lia).
    lia.
  - apply in_map.
    unfold Znth.
    apply nth_In.
    rewrite <- z_to_nat_Zlength.
    lia.
Qed.

Lemma encode_char_z_correct : forall c,
  is_upper_z c \/ is_lower_z c \/ is_space_z c ->
  encode_char_spec (ascii_of_z c) (ascii_of_z (encode_char_z c)).
Proof.
  intros c Hclass.
  assert (
    c = 32 \/
    c = 65 \/ c = 66 \/ c = 67 \/ c = 68 \/ c = 69 \/ c = 70 \/
    c = 71 \/ c = 72 \/ c = 73 \/ c = 74 \/ c = 75 \/ c = 76 \/
    c = 77 \/ c = 78 \/ c = 79 \/ c = 80 \/ c = 81 \/ c = 82 \/
    c = 83 \/ c = 84 \/ c = 85 \/ c = 86 \/ c = 87 \/ c = 88 \/
    c = 89 \/ c = 90 \/
    c = 97 \/ c = 98 \/ c = 99 \/ c = 100 \/ c = 101 \/ c = 102 \/
    c = 103 \/ c = 104 \/ c = 105 \/ c = 106 \/ c = 107 \/ c = 108 \/
    c = 109 \/ c = 110 \/ c = 111 \/ c = 112 \/ c = 113 \/ c = 114 \/
    c = 115 \/ c = 116 \/ c = 117 \/ c = 118 \/ c = 119 \/ c = 120 \/
    c = 121 \/ c = 122) as Hcases
    by (unfold is_upper_z, is_lower_z, is_space_z in *; lia).
  repeat
    match type of Hcases with
    | _ \/ _ => destruct Hcases as [-> | Hcases]; [vm_compute; reflexivity |]
    | _ => subst c; vm_compute; reflexivity
    end.
Qed.

Lemma problem_93_spec_z_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_93_pre_z input ->
  ascii_range_z input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encode_char_z (Znth k input 0)) ->
  problem_93_spec_z input output.
Proof.
  intros input.
  induction input as [| x xs IH]; intros output n Hin Hout Hpre Hrange Hpoint.
  - destruct output; simpl in *.
    + unfold problem_93_spec_z, problem_93_spec. simpl. constructor.
    + rewrite Zlength_nil in Hin.
      rewrite Zlength_cons in Hout.
      pose proof (Zlength_nonneg output).
      lia.
  - destruct output as [| y ys].
    + rewrite Zlength_cons in Hin.
      rewrite Zlength_nil in Hout.
      pose proof (Zlength_nonneg xs).
      lia.
    + unfold problem_93_spec_z, problem_93_spec in *.
      simpl.
      constructor.
      * assert (Hclass :
          is_upper_z x \/ is_lower_z x \/ is_space_z x).
        {
          eapply problem_93_pre_z_char with (s := x :: xs) (k := 0);
            try exact Hpre; try exact Hrange.
          rewrite Zlength_cons.
          pose proof (Zlength_nonneg xs).
          lia.
        }
        specialize (Hpoint 0).
        change (Znth 0 (y :: ys) 0) with y in Hpoint.
        change (Znth 0 (x :: xs) 0) with x in Hpoint.
        rewrite Hpoint by (rewrite Zlength_cons in Hin; pose proof (Zlength_nonneg xs); lia).
        apply encode_char_z_correct.
        exact Hclass.
      * eapply IH with (n := n - 1).
        -- rewrite Zlength_cons in Hin. lia.
        -- rewrite Zlength_cons in Hout. lia.
        -- unfold problem_93_pre_z, problem_93_pre in *.
           rewrite list_ascii_of_string_string_of_list_z in Hpre.
           simpl in Hpre.
           inversion Hpre as [| ? ? _ Htail]; subst.
           rewrite list_ascii_of_string_string_of_list_z.
           exact Htail.
        -- unfold ascii_range_z in *.
           intros i Hi.
           specialize (Hrange (i + 1)).
           replace (Znth i xs 0) with (Znth (i + 1) (x :: xs) 0).
           apply Hrange.
           rewrite Zlength_cons.
           lia.
           unfold Znth.
           replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
           reflexivity.
        -- intros k Hk.
           specialize (Hpoint (k + 1)).
           replace (Znth k ys 0) with (Znth (k + 1) (y :: ys) 0).
           2:{
             unfold Znth.
             replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
             reflexivity.
           }
           replace (Znth k xs 0) with (Znth (k + 1) (x :: xs) 0).
           2:{
             unfold Znth.
             replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
             reflexivity.
           }
           apply Hpoint.
           lia.
Qed.
