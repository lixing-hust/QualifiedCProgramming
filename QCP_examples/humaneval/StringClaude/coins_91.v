Load "../spec/91".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition zbool (b : bool) : Z := if b then 1 else 0.

Definition z_is_space (c : Z) : bool := Z.eqb c 32.
Definition z_is_i (c : Z) : bool := Z.eqb c 73.
Definition z_is_delim (c : Z) : bool :=
  orb (orb (Z.eqb c 46) (Z.eqb c 63)) (Z.eqb c 33).

Definition bored_add_z (c isi : Z) : Z :=
  zbool (andb (z_is_space c) (Z.eqb isi 1)).

Definition bored_next_isi_z (c isstart : Z) : Z :=
  zbool (andb (z_is_i c) (Z.eqb isstart 1)).

Definition bored_next_isstart_z (c isstart : Z) : Z :=
  if z_is_delim c then 1
  else if z_is_space c then isstart
  else 0.

Fixpoint bored_state_after_nat (k : nat) (l : list Z) : Z * Z * Z :=
  match k with
  | O => (0, 1, 0)
  | S k' =>
      let '(sum, isstart, isi) := bored_state_after_nat k' l in
      let c := Znth (Z.of_nat k') l 0 in
      (sum + bored_add_z c isi,
       bored_next_isstart_z c isstart,
       bored_next_isi_z c isstart)
  end.

Definition bored_sum_prefix_z (i : Z) (l : list Z) : Z :=
  let '(sum, _, _) := bored_state_after_nat (Z.to_nat i) l in sum.

Definition bored_isstart_prefix_z (i : Z) (l : list Z) : Z :=
  let '(_, isstart, _) := bored_state_after_nat (Z.to_nat i) l in isstart.

Definition bored_isi_prefix_z (i : Z) (l : list Z) : Z :=
  let '(_, _, isi) := bored_state_after_nat (Z.to_nat i) l in isi.

Definition problem_91_pre_z (s : list Z) : Prop :=
  problem_91_pre (string_of_list_z s).

Definition problem_91_spec_z (s : list Z) (output : Z) : Prop :=
  problem_91_spec (string_of_list_z s) (Z.to_nat output).

Lemma bored_state_after_step : forall i l sum isstart isi,
  0 <= i ->
  bored_state_after_nat (Z.to_nat i) l = (sum, isstart, isi) ->
  bored_state_after_nat (Z.to_nat (i + 1)) l =
    (sum + bored_add_z (Znth i l 0) isi,
     bored_next_isstart_z (Znth i l 0) isstart,
     bored_next_isi_z (Znth i l 0) isstart).
Proof.
  intros i l sum isstart isi Hi Hstate.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite Hstate.
  reflexivity.
Qed.

Lemma bored_sum_prefix_step : forall i l,
  0 <= i ->
  bored_sum_prefix_z (i + 1) l =
  bored_sum_prefix_z i l +
  bored_add_z (Znth i l 0) (bored_isi_prefix_z i l).
Proof.
  intros i l Hi.
  unfold bored_sum_prefix_z, bored_isi_prefix_z.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_isstart_prefix_step : forall i l,
  0 <= i ->
  bored_isstart_prefix_z (i + 1) l =
  bored_next_isstart_z (Znth i l 0) (bored_isstart_prefix_z i l).
Proof.
  intros i l Hi.
  unfold bored_isstart_prefix_z.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_isi_prefix_step : forall i l,
  0 <= i ->
  bored_isi_prefix_z (i + 1) l =
  bored_next_isi_z (Znth i l 0) (bored_isstart_prefix_z i l).
Proof.
  intros i l Hi.
  unfold bored_isi_prefix_z, bored_isstart_prefix_z.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_add_z_range : forall c isi,
  0 <= bored_add_z c isi <= 1.
Proof.
  unfold bored_add_z, zbool.
  intros.
  destruct (z_is_space c && (isi =? 1)); lia.
Qed.

Lemma bored_next_isi_z_range : forall c isstart,
  bored_next_isi_z c isstart = 0 \/ bored_next_isi_z c isstart = 1.
Proof.
  unfold bored_next_isi_z, zbool.
  intros.
  destruct (z_is_i c && (isstart =? 1)); lia.
Qed.

Lemma bored_next_isstart_z_range : forall c isstart,
  (isstart = 0 \/ isstart = 1) ->
  bored_next_isstart_z c isstart = 0 \/ bored_next_isstart_z c isstart = 1.
Proof.
  unfold bored_next_isstart_z.
  intros c isstart Hrange.
  destruct (z_is_delim c); auto.
  destruct (z_is_space c); auto.
Qed.

Lemma bored_state_after_nat_range : forall n l sum isstart isi,
  bored_state_after_nat n l = (sum, isstart, isi) ->
  0 <= sum <= Z.of_nat n /\
  (isstart = 0 \/ isstart = 1) /\
  (isi = 0 \/ isi = 1).
Proof.
  induction n as [| n IH]; intros l sum isstart isi Hstate.
  - simpl in Hstate.
    inversion Hstate; subst.
    repeat split; lia.
  - simpl in Hstate.
    destruct (bored_state_after_nat n l) as [[sum0 isstart0] isi0] eqn:Hprev.
    inversion Hstate; subst; clear Hstate.
    specialize (IH l sum0 isstart0 isi0 Hprev).
    destruct IH as [Hsum [Hisstart Hisi]].
    pose proof (bored_add_z_range (Znth (Z.of_nat n) l 0) isi0) as Hadd.
    split.
    + lia.
    + split.
      * apply bored_next_isstart_z_range.
        exact Hisstart.
      * apply bored_next_isi_z_range.
Qed.

Lemma bored_state_range : forall i l,
  0 <= i ->
  0 <= bored_sum_prefix_z i l <= i /\
  (bored_isstart_prefix_z i l = 0 \/ bored_isstart_prefix_z i l = 1) /\
  (bored_isi_prefix_z i l = 0 \/ bored_isi_prefix_z i l = 1).
Proof.
  intros i l Hi.
  unfold bored_sum_prefix_z, bored_isstart_prefix_z, bored_isi_prefix_z.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  pose proof (bored_state_after_nat_range (Z.to_nat i) l sum isstart isi Hstate) as Hrange.
  rewrite Z2Nat.id in Hrange by lia.
  exact Hrange.
Qed.

Definition bored_step_z_state (st : Z * Z * Z) (c : Z) : Z * Z * Z :=
  let '(sum, isstart, isi) := st in
  (sum + bored_add_z c isi,
   bored_next_isstart_z c isstart,
   bored_next_isi_z c isstart).

Fixpoint bored_state_list_z (l : list Z) (st : Z * Z * Z) : Z * Z * Z :=
  match l with
  | [] => st
  | c :: rest => bored_state_list_z rest (bored_step_z_state st c)
  end.

Definition bored_step_ascii_state
    (st : nat * bool * bool) (c : ascii) : nat * bool * bool :=
  let '(sum, isstart, isi) := st in
  let add := if andb (Ascii.eqb c " "%char) isi then 1%nat else 0%nat in
  let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
  let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
  let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
  ((sum + add)%nat, isstart', isi').

Fixpoint bored_state_list_ascii
    (l : list ascii) (st : nat * bool * bool) : nat * bool * bool :=
  match l with
  | [] => st
  | c :: rest => bored_state_list_ascii rest (bored_step_ascii_state st c)
  end.

Fixpoint is_bored_ascii_list (l : list ascii) (isstart isi : bool) : nat :=
  match l with
  | [] => 0%nat
  | c :: rest =>
      let add := if andb (Ascii.eqb c " "%char) isi then 1%nat else 0%nat in
      let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
      let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
      let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
      (add + is_bored_ascii_list rest isstart' isi')%nat
  end.

Definition state_rel (zst : Z * Z * Z) (ast : nat * bool * bool) : Prop :=
  let '(zsum, zisstart, zisi) := zst in
  let '(asum, aisstart, aisi) := ast in
  zsum = Z.of_nat asum /\ zisstart = zbool aisstart /\ zisi = zbool aisi.

Lemma bored_state_list_z_app : forall l1 l2 st,
  bored_state_list_z (l1 ++ l2) st =
  bored_state_list_z l2 (bored_state_list_z l1 st).
Proof.
  induction l1 as [| c rest IH]; intros l2 st; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma bored_state_list_z_snoc : forall l c st,
  bored_state_list_z (l ++ [c]) st =
  bored_step_z_state (bored_state_list_z l st) c.
Proof.
  intros l c st.
  rewrite bored_state_list_z_app.
  reflexivity.
Qed.

Lemma firstn_succ_snoc_91 : forall {A : Type} n (l : list A) d,
  (n < Datatypes.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; simpl in *; try lia. reflexivity.
  - destruct l; simpl in *; try lia.
    rewrite (IH l d) by lia. reflexivity.
Qed.

Lemma Znth_of_nat_nth_91 : forall {A : Type} (l : list A) n d,
  (n < Datatypes.length l)%nat ->
  Znth (Z.of_nat n) l d = nth n l d.
Proof.
  intros A l n d Hn.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma bored_state_after_nat_firstn : forall n l,
  (n <= Datatypes.length l)%nat ->
  bored_state_after_nat n l =
  bored_state_list_z (firstn n l) (0, 1, 0).
Proof.
  induction n as [| n IH]; intros l Hn.
  - reflexivity.
  - cbn [bored_state_after_nat].
    rewrite IH by lia.
    rewrite firstn_succ_snoc_91 with (d := 0) by lia.
    rewrite bored_state_list_z_snoc.
    rewrite Znth_of_nat_nth_91 by lia.
    destruct (bored_state_list_z (firstn n l) (0, 1, 0)) as [[sum isstart] isi].
    reflexivity.
Qed.

Lemma ascii_eqb_ascii_of_z_const : forall x n,
  0 <= x < 256 ->
  (n < 256)%nat ->
  Ascii.eqb (ascii_of_z x) (ascii_of_nat n) = Z.eqb x (Z.of_nat n).
Proof.
  intros x n Hx Hn.
  destruct (Ascii.eqb_spec (ascii_of_z x) (ascii_of_nat n)) as [Heq | Hneq];
  destruct (Z.eqb_spec x (Z.of_nat n)) as [Hz | Hnz]; try reflexivity.
  - exfalso.
    apply Hnz.
    apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z in Heq by exact Hx.
    rewrite nat_ascii_embedding in Heq by lia.
    lia.
  - subst x.
    exfalso.
    apply Hneq.
    apply ascii_of_z_eq_ascii_of_nat.
    reflexivity.
Qed.

Lemma z_is_space_ascii : forall c,
  0 <= c < 256 ->
  z_is_space c = Ascii.eqb (ascii_of_z c) " "%char.
Proof.
  intros c Hc.
  unfold z_is_space.
  change " "%char with (ascii_of_nat 32).
  rewrite ascii_eqb_ascii_of_z_const by lia.
  reflexivity.
Qed.

Lemma z_is_i_ascii : forall c,
  0 <= c < 256 ->
  z_is_i c = Ascii.eqb (ascii_of_z c) "I"%char.
Proof.
  intros c Hc.
  unfold z_is_i.
  change "I"%char with (ascii_of_nat 73).
  rewrite ascii_eqb_ascii_of_z_const by lia.
  reflexivity.
Qed.

Lemma is_sentence_delimiter_eqb_91 : forall c,
  is_sentence_delimiter c =
  orb (orb (Ascii.eqb c "."%char) (Ascii.eqb c "?"%char))
      (Ascii.eqb c "!"%char).
Proof.
  intros [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Lemma z_is_delim_ascii : forall c,
  0 <= c < 256 ->
  z_is_delim c = is_sentence_delimiter (ascii_of_z c).
Proof.
  intros c Hc.
  unfold z_is_delim.
  rewrite is_sentence_delimiter_eqb_91.
  change "."%char with (ascii_of_nat 46).
  change "?"%char with (ascii_of_nat 63).
  change "!"%char with (ascii_of_nat 33).
  repeat match goal with
  | |- context[Ascii.eqb (ascii_of_z c) (ascii_of_nat ?n)] =>
      rewrite (ascii_eqb_ascii_of_z_const c n) by lia
  end.
  reflexivity.
Qed.

Lemma bored_step_state_rel : forall zst ast c,
  0 <= c < 256 ->
  state_rel zst ast ->
  state_rel (bored_step_z_state zst c)
            (bored_step_ascii_state ast (ascii_of_z c)).
Proof.
  intros [[zsum zisstart] zisi] [[asum aisstart] aisi] c Hc Hrel.
  unfold state_rel in Hrel.
  simpl in Hrel.
  destruct Hrel as [Hsum [Hstart Hisi]].
  subst zsum zisstart zisi.
  unfold state_rel, bored_step_z_state, bored_step_ascii_state,
         bored_add_z, bored_next_isstart_z, bored_next_isi_z, zbool.
  rewrite z_is_space_ascii by exact Hc.
  rewrite z_is_i_ascii by exact Hc.
  rewrite z_is_delim_ascii by exact Hc.
  remember (Ascii.eqb (ascii_of_z c) " "%char) as is_space.
  remember (Ascii.eqb (ascii_of_z c) "I"%char) as is_i.
  remember (is_sentence_delimiter (ascii_of_z c)) as is_delim.
  destruct is_space, is_i, is_delim, aisstart, aisi;
    simpl; repeat split; rewrite ?Nat2Z.inj_add; simpl; lia.
Qed.

Lemma ascii_range_z_Forall : forall l,
  ascii_range_z l ->
  Forall (fun c => 0 <= c < 256) l.
Proof.
  induction l as [| c rest IH]; intros Hrange.
  - constructor.
  - constructor.
    + specialize (Hrange 0).
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
    + apply IH.
      intros i Hi.
      specialize (Hrange (i + 1)).
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons. lia.
Qed.

Lemma bored_state_list_rel_gen : forall l zst ast,
  Forall (fun c => 0 <= c < 256) l ->
  state_rel zst ast ->
  state_rel (bored_state_list_z l zst)
            (bored_state_list_ascii (map ascii_of_z l) ast).
Proof.
  induction l as [| c rest IH]; intros zst ast Hall Hrel.
  - exact Hrel.
  - inversion Hall as [| ? ? Hc Hrest]; subst.
    simpl.
    apply IH.
    + exact Hrest.
    + apply bored_step_state_rel; assumption.
Qed.

Lemma bored_state_list_rel : forall l,
  Forall (fun c => 0 <= c < 256) l ->
  state_rel (bored_state_list_z l (0, 1, 0))
            (bored_state_list_ascii (map ascii_of_z l) (0%nat, true, false)).
Proof.
  intros l Hall.
  apply bored_state_list_rel_gen.
  - exact Hall.
  - repeat split; reflexivity.
Qed.

Lemma bored_state_list_ascii_sum : forall chars sum isstart isi,
  let '(sum', _, _) := bored_state_list_ascii chars (sum, isstart, isi) in
  sum' = (sum + is_bored_ascii_list chars isstart isi)%nat.
Proof.
  induction chars as [| c rest IH]; intros sum isstart isi; simpl.
  - lia.
  - unfold bored_step_ascii_state.
    remember (if (c =? " ")%char && isi then 1%nat else 0%nat) as add.
    remember (if (c =? "I")%char && isstart then true else false) as isi'.
    remember (if is_sentence_delimiter c
              then true
              else if (c =? " ")%char then isstart else false) as isstart'.
    destruct (bored_state_list_ascii rest ((sum + add)%nat, isstart', isi'))
      as [[sum' isstart''] isi''] eqn:Hstate.
    specialize (IH (sum + add)%nat isstart' isi').
    rewrite Hstate in IH.
    simpl in IH.
    lia.
Qed.

Lemma is_bored_aux_string_of_list_z : forall l isstart isi,
  is_bored_aux (string_of_list_z l) isstart isi =
  is_bored_ascii_list (map ascii_of_z l) isstart isi.
Proof.
  induction l as [| c rest IH]; intros isstart isi; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma bored_sum_prefix_z_correct : forall s,
  ascii_range_z s ->
  Z.to_nat (bored_sum_prefix_z (Zlength s) s) =
  is_bored_impl (string_of_list_z s).
Proof.
  intros s Hrange.
  unfold bored_sum_prefix_z.
  rewrite z_to_nat_Zlength.
  rewrite bored_state_after_nat_firstn by lia.
  rewrite firstn_all.
  pose proof (bored_state_list_rel s (ascii_range_z_Forall s Hrange)) as Hrel.
  destruct (bored_state_list_z s (0, 1, 0)) as [[zsum zisstart] zisi].
  destruct (bored_state_list_ascii (map ascii_of_z s) (0%nat, true, false))
    as [[asum aisstart] aisi] eqn:Hascii.
  unfold state_rel in Hrel.
  simpl in Hrel.
  destruct Hrel as [Hsum _].
  rewrite Hsum.
  rewrite Nat2Z.id.
  unfold is_bored_impl.
  rewrite is_bored_aux_string_of_list_z.
  pose proof (bored_state_list_ascii_sum (map ascii_of_z s) 0 true false) as Hsum_ascii.
  rewrite Hascii in Hsum_ascii.
  simpl in Hsum_ascii.
  exact Hsum_ascii.
Qed.

Lemma problem_91_spec_z_intro : forall s output,
  ascii_range_z s ->
  output = bored_sum_prefix_z (Zlength s) s ->
  problem_91_spec_z s output.
Proof.
  intros s output Hrange Hout.
  unfold problem_91_spec_z, problem_91_spec.
  rewrite Hout.
  apply bored_sum_prefix_z_correct.
  exact Hrange.
Qed.
