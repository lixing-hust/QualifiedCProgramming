Load "../spec/22".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition py_value_tag (v : py_value) : Z :=
  match v with
  | PyInt _ => 0
  | PyFloat => 1
  | PyString _ => 2
  | PyDict => 2
  | PyList => 2
  end.

Definition py_value_payload (v : py_value) : Z :=
  match v with
  | PyInt n => n
  | _ => 0
  end.

Definition py_value_tags (input : list py_value) : list Z :=
  map py_value_tag input.

Definition py_value_payloads (input : list py_value) : list Z :=
  map py_value_payload input.

Fixpoint filter_integer_values (input : list py_value) : list Z :=
  match input with
  | [] => []
  | PyInt n :: xs => n :: filter_integer_values xs
  | _ :: xs => filter_integer_values xs
  end.

Fixpoint filter_tagged (types values : list Z) : list Z :=
  match types, values with
  | t :: ts, v :: vs =>
      if Z.eqb t 0 then v :: filter_tagged ts vs
      else filter_tagged ts vs
  | _, _ => []
  end.

Definition problem_22_pre_z (input : list py_value) : Prop :=
  problem_22_pre input.

Definition problem_22_spec_z (input : list py_value) (output : list Z) : Prop :=
  problem_22_spec input (map PyInt output).

Lemma filter_tagged_encoded : forall input,
  filter_tagged (py_value_tags input) (py_value_payloads input) =
  filter_integer_values input.
Proof.
  induction input as [|v input IH]; simpl; [reflexivity|].
  destruct v; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma is_subsequence_weaken_right : forall (A : Type) (out input : list A) x,
  is_subsequence out input -> is_subsequence out (x :: input).
Proof.
  intros A out input x Hsub.
  destruct out as [|y ys]; simpl; [exact I|].
  simpl. right. exact Hsub.
Qed.

Lemma filtered_pyints_subsequence : forall input,
  is_subsequence (map PyInt (filter_integer_values input)) input.
Proof.
  induction input as [|v input IH]; simpl; [exact I|].
  destruct v; simpl.
  - left. split; [reflexivity|exact IH].
  - apply is_subsequence_weaken_right. exact IH.
  - apply is_subsequence_weaken_right. exact IH.
  - apply is_subsequence_weaken_right. exact IH.
  - apply is_subsequence_weaken_right. exact IH.
Qed.

Lemma in_filter_integer_values : forall input n,
  In n (filter_integer_values input) <-> In (PyInt n) input.
Proof.
  induction input as [|v input IH]; intros n; simpl; [tauto|].
  destruct v; simpl.
  - rewrite IH. split.
    + intros [H|H].
      * left. subst. reflexivity.
      * right. exact H.
    + intros [H|H].
      * inversion H. left. reflexivity.
      * right. exact H.
  - rewrite IH. split; intros H; [right|].
    + exact H.
    + destruct H as [H|H]; [discriminate|exact H].
  - rewrite IH. split; intros H; [right|].
    + exact H.
    + destruct H as [H|H]; [discriminate|exact H].
  - rewrite IH. split; intros H; [right|].
    + exact H.
    + destruct H as [H|H]; [discriminate|exact H].
  - rewrite IH. split; intros H; [right|].
    + exact H.
    + destruct H as [H|H]; [discriminate|exact H].
Qed.

Lemma problem_22_spec_filter_integer_values : forall input,
  problem_22_spec_z input (filter_integer_values input).
Proof.
  intros input.
  unfold problem_22_spec_z, problem_22_spec.
  split.
  - apply filtered_pyints_subsequence.
  - intros v. split.
    + intros Hin.
      apply in_map_iff in Hin.
      destruct Hin as [n [Hv Hn]]. subst v.
      split.
      * apply (proj1 (in_filter_integer_values input n)). exact Hn.
      * simpl. exact I.
    + intros [Hin Hint].
      destruct v as [n|s| | |]; simpl in Hint.
      * apply in_map. apply (proj2 (in_filter_integer_values input n)). exact Hin.
      * contradiction.
      * contradiction.
      * contradiction.
      * contradiction.
Qed.

Lemma problem_22_spec_z_of_filter_tagged : forall input types values output,
  types = py_value_tags input ->
  values = py_value_payloads input ->
  output = filter_tagged types values ->
  problem_22_spec_z input output.
Proof.
  intros input types values output Htypes Hvalues Houtput.
  subst types. subst values. subst output.
  rewrite filter_tagged_encoded.
  apply problem_22_spec_filter_integer_values.
Qed.

Lemma filter_tagged_snoc : forall types values t v,
  length types = length values ->
  filter_tagged (types ++ [t]) (values ++ [v]) =
  filter_tagged types values ++
    (if Z.eqb t 0 then [v] else []).
Proof.
  induction types as [|x xs IH]; intros values t v Hlen.
  - destruct values; [simpl; destruct (Z.eqb t 0); reflexivity|discriminate].
  - destruct values as [|y ys]; [discriminate|].
    simpl in Hlen. inversion Hlen as [Htail].
    simpl. destruct (Z.eqb x 0); simpl; rewrite IH by exact Htail; reflexivity.
Qed.

Lemma filter_tagged_prefix_int : forall types values i,
  Zlength types = Zlength values ->
  0 <= i < Zlength types ->
  Znth i types 0 = 0 ->
  filter_tagged (sublist 0 (i + 1) types) (sublist 0 (i + 1) values) =
  filter_tagged (sublist 0 i types) (sublist 0 i values) ++
    [Znth i values 0].
Proof.
  intros types values i Hlen Hi Htag.
  rewrite (sublist_split 0 (i + 1) i types) by lia.
  rewrite (sublist_split 0 (i + 1) i values) by lia.
  rewrite (sublist_single 0 i types) by lia.
  rewrite (sublist_single 0 i values) by lia.
  rewrite filter_tagged_snoc.
  - rewrite Htag. reflexivity.
  - rewrite !sublist_length by lia. reflexivity.
Qed.

Lemma filter_tagged_prefix_nonint : forall types values i,
  Zlength types = Zlength values ->
  0 <= i < Zlength types ->
  Znth i types 0 <> 0 ->
  filter_tagged (sublist 0 (i + 1) types) (sublist 0 (i + 1) values) =
  filter_tagged (sublist 0 i types) (sublist 0 i values).
Proof.
  intros types values i Hlen Hi Htag.
  rewrite (sublist_split 0 (i + 1) i types) by lia.
  rewrite (sublist_split 0 (i + 1) i values) by lia.
  rewrite (sublist_single 0 i types) by lia.
  rewrite (sublist_single 0 i values) by lia.
  rewrite filter_tagged_snoc.
  - apply Z.eqb_neq in Htag. rewrite Htag. rewrite app_nil_r. reflexivity.
  - rewrite !sublist_length by lia. reflexivity.
Qed.
