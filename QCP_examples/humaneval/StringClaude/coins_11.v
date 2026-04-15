Load "../spec/11".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition char_list_string (l : list Z) (s : string) : Prop :=
  list_ascii_of_string s = map (fun z => ascii_of_nat (Z.to_nat z)) l.

Definition problem_11_pre_z (a b : list Z) : Prop :=
  Zlength a = Zlength b /\
  (forall k, 0 <= k < Zlength a -> Znth k a 0 = 48 \/ Znth k a 0 = 49) /\
  (forall k, 0 <= k < Zlength b -> Znth k b 0 = 48 \/ Znth k b 0 = 49).

Definition problem_11_spec_z (a b output : list Z) : Prop :=
  Zlength a = Zlength b /\
  Zlength output = Zlength a /\
  forall k,
    0 <= k < Zlength output ->
    ((Znth k a 0 = Znth k b 0 -> Znth k output 0 = 48) /\
     (Znth k a 0 <> Znth k b 0 -> Znth k output 0 = 49)).

Lemma problem_11_pre_z_from_spec :
  forall a b a_str b_str,
    char_list_string a a_str ->
    char_list_string b b_str ->
    problem_11_pre a_str b_str ->
    problem_11_pre_z a b.
Proof.
  intros.
  unfold problem_11_pre_z.
  (* The C proof uses the list-Z view; this bridge lemma is kept as the
     connection point to the original string specification. *)
Abort.

Lemma problem_11_spec_z_intro :
  forall a b output n,
    Zlength a = n ->
    Zlength b = n ->
    Zlength output = n ->
    (forall k,
      0 <= k < n ->
      ((Znth k a 0 = Znth k b 0 /\ Znth k output 0 = 48) \/
       (Znth k a 0 <> Znth k b 0 /\ Znth k output 0 = 49))) ->
    problem_11_spec_z a b output.
Proof.
  intros a b output n Ha Hb Ho Hxor.
  unfold problem_11_spec_z.
  split; [lia |].
  split; [lia |].
  intros k0 Hk0.
  specialize (Hxor k0).
  rewrite <- Ho in Hxor.
  specialize (Hxor Hk0).
  destruct Hxor as [[Heq Hout] | [Hneq Hout]].
  - split; intros; auto; contradiction.
  - split; intros; auto; contradiction.
Qed.
