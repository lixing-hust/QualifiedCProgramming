Load "../spec/140".

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
Local Open Scope list_scope.

Definition problem_140_pre_z (s : list Z) : Prop :=
  problem_140_pre (string_of_list_z s).

Definition problem_140_spec_z (input output : list Z) : Prop :=
  problem_140_spec (string_of_list_z input) (string_of_list_z output).

Definition ascii_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition flush_spaces_z (n : Z) : list Z :=
  if Z.eqb n 0 then []
  else if Z.eqb n 1 then [95]
  else if Z.eqb n 2 then [95; 95]
  else [45].

Definition flush_spaces_len_z (n : Z) : Z :=
  if Z.eqb n 0 then 0
  else if Z.eqb n 1 then 1
  else if Z.eqb n 2 then 2
  else 1.

Definition scan_step_z (st : list Z * Z) (c : Z) : list Z * Z :=
  let '(out, pending) := st in
  if Z.eqb c 32 then
    (out, pending + 1)
  else
    (out ++ flush_spaces_z pending ++ [c], 0).

Definition fix_spaces_state_z (i : Z) (s : list Z) : list Z * Z :=
  fold_left scan_step_z (firstn (Z.to_nat i) s) ([], 0).

Definition fix_spaces_prefix_z (i : Z) (s : list Z) : list Z :=
  fst (fix_spaces_state_z i s).

Definition fix_spaces_pending_z (i : Z) (s : list Z) : Z :=
  snd (fix_spaces_state_z i s).

Definition fix_spaces_output_z (s : list Z) : list Z :=
  fix_spaces_prefix_z (Zlength s) s ++
  flush_spaces_z (fix_spaces_pending_z (Zlength s) s).

Lemma flush_spaces_z_length : forall n,
  0 <= n ->
  Zlength (flush_spaces_z n) = flush_spaces_len_z n.
Proof.
  intros n Hn.
  unfold flush_spaces_z, flush_spaces_len_z.
  destruct (Z.eqb_spec n 0); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 1); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 2); subst; simpl; [reflexivity |].
  reflexivity.
Qed.

Lemma flush_spaces_len_bound : forall n,
  0 <= n -> flush_spaces_len_z n <= n.
Proof.
  intros n Hn.
  unfold flush_spaces_len_z.
  destruct (Z.eqb_spec n 0); subst; simpl; [lia |].
  destruct (Z.eqb_spec n 1); subst; simpl; [lia |].
  destruct (Z.eqb_spec n 2); subst; simpl; [lia |].
  lia.
Qed.

Lemma fix_spaces_state_z_0 : forall s,
  fix_spaces_prefix_z 0 s = [] /\
  fix_spaces_pending_z 0 s = 0.
Proof.
  intros s.
  unfold fix_spaces_prefix_z, fix_spaces_pending_z, fix_spaces_state_z.
  simpl.
  split; reflexivity.
Qed.

Lemma fold_left_scan_step_app : forall xs ys st,
  fold_left scan_step_z (xs ++ ys) st =
  fold_left scan_step_z ys (fold_left scan_step_z xs st).
Proof.
  induction xs as [| x xs IH]; intros ys st; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma firstn_succ_snoc_140 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_140 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_140 with (d := 0) by (rewrite <- z_to_nat_Zlength; lia).
  reflexivity.
Qed.

Lemma fix_spaces_state_z_step : forall i s,
  0 <= i < Zlength s ->
  fix_spaces_state_z (i + 1) s =
  scan_step_z (fix_spaces_state_z i s) (Znth i s 0).
Proof.
  intros i s H.
  unfold fix_spaces_state_z.
  rewrite firstn_succ_Znth_140 by lia.
  rewrite fold_left_scan_step_app.
  reflexivity.
Qed.

Lemma fix_spaces_step_space : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 = 32 ->
  fix_spaces_prefix_z (i + 1) s = fix_spaces_prefix_z i s /\
  fix_spaces_pending_z (i + 1) s = fix_spaces_pending_z i s + 1.
Proof.
  intros i s Hi Hc.
  unfold fix_spaces_prefix_z, fix_spaces_pending_z.
  rewrite fix_spaces_state_z_step by lia.
  unfold scan_step_z.
  rewrite Hc.
  change (32 =? 32) with true.
  destruct (fix_spaces_state_z i s).
  split; reflexivity.
Qed.

Lemma fix_spaces_step_nonspace : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_prefix_z (i + 1) s =
    fix_spaces_prefix_z i s ++ flush_spaces_z (fix_spaces_pending_z i s) ++ [Znth i s 0] /\
  fix_spaces_pending_z (i + 1) s = 0.
Proof.
  intros i s Hi Hc.
  unfold fix_spaces_prefix_z, fix_spaces_pending_z.
  rewrite fix_spaces_state_z_step by lia.
  unfold scan_step_z.
  destruct (Z.eqb_spec (Znth i s 0) 32); [contradiction |].
  destruct (fix_spaces_state_z i s).
  split; reflexivity.
Qed.

Lemma fix_spaces_state_bound : forall i s,
  0 <= i ->
  i <= Zlength s ->
  0 <= fix_spaces_pending_z i s /\
  Zlength (fix_spaces_prefix_z i s) + fix_spaces_pending_z i s <= i.
Proof.
  intros i s Hi.
  remember (Z.to_nat i) as ni eqn:Hni.
  revert i Hi Hni.
  induction ni as [| ni IH]; intros i Hi Hni Hile.
  - assert (i = 0) by lia.
    subst i.
    destruct (fix_spaces_state_z_0 s) as [Hp Hpend].
    rewrite Hp, Hpend, Zlength_nil.
    lia.
  - assert (0 < i) by lia.
    pose (j := i - 1).
    assert (Hj_nonneg : 0 <= j) by (unfold j; lia).
    assert (Hj_len : j < Zlength s) by (unfold j; lia).
    assert (Hj_to_nat : Z.to_nat j = ni) by (unfold j; lia).
    specialize (IH j Hj_nonneg ltac:(symmetry; exact Hj_to_nat) ltac:(unfold j; lia)).
    destruct IH as [Hpend_nonneg Hbound].
    assert (Hi_eq : i = j + 1) by (unfold j; lia).
    rewrite Hi_eq.
    destruct (Z.eq_dec (Znth j s 0) 32) as [Hspace | Hnonspace].
    + destruct (fix_spaces_step_space j s ltac:(lia) Hspace) as [Hp Hpend].
      rewrite Hp, Hpend.
      lia.
    + destruct (fix_spaces_step_nonspace j s ltac:(lia) Hnonspace) as [Hp Hpend].
      rewrite Hp, Hpend.
      rewrite !Zlength_app, flush_spaces_z_length, Zlength_cons, Zlength_nil by lia.
      pose proof (flush_spaces_len_bound (fix_spaces_pending_z j s) Hpend_nonneg).
      lia.
Qed.

Lemma fix_spaces_prefix_bound : forall i s,
  0 <= i ->
  i <= Zlength s ->
  Zlength (fix_spaces_prefix_z i s) <= i.
Proof.
  intros i s Hi Hile.
  pose proof (fix_spaces_state_bound i s Hi Hile) as [Hpend Hbound].
  lia.
Qed.

Lemma fix_spaces_output_length_bound : forall s,
  Zlength (fix_spaces_output_z s) <= Zlength s.
Proof.
  intros s.
  unfold fix_spaces_output_z.
  rewrite Zlength_app, flush_spaces_z_length.
  - pose proof (fix_spaces_state_bound (Zlength s) s ltac:(apply Zlength_nonneg) ltac:(lia))
      as [Hpend Hbound].
    pose proof (flush_spaces_len_bound (fix_spaces_pending_z (Zlength s) s) Hpend).
    lia.
  - pose proof (fix_spaces_state_bound (Zlength s) s ltac:(apply Zlength_nonneg) ltac:(lia))
      as [Hpend _].
    exact Hpend.
Qed.

Lemma fix_spaces_step_nonspace_pending0 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending_z i s = 0 ->
  fix_spaces_prefix_z (i + 1) s =
    fix_spaces_prefix_z i s ++ [Znth i s 0] /\
  fix_spaces_pending_z (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split; [reflexivity | exact Hpend].
Qed.

Lemma fix_spaces_step_nonspace_pending1 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending_z i s = 1 ->
  fix_spaces_prefix_z (i + 1) s =
    (fix_spaces_prefix_z i s ++ [95]) ++ [Znth i s 0] /\
  fix_spaces_pending_z (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split; [rewrite <- app_assoc; reflexivity | exact Hpend].
Qed.

Lemma fix_spaces_step_nonspace_pending2 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending_z i s = 2 ->
  fix_spaces_prefix_z (i + 1) s =
    ((fix_spaces_prefix_z i s ++ [95]) ++ [95]) ++ [Znth i s 0] /\
  fix_spaces_pending_z (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split.
  - repeat rewrite <- app_assoc; reflexivity.
  - exact Hpend.
Qed.

Lemma fix_spaces_step_nonspace_pending_more : forall i s p,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  p = fix_spaces_pending_z i s ->
  p > 2 ->
  fix_spaces_prefix_z (i + 1) s =
    (fix_spaces_prefix_z i s ++ [45]) ++ [Znth i s 0] /\
  fix_spaces_pending_z (i + 1) s = 0.
Proof.
  intros i s p Hi Hc Hp Hmore.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hpref Hpend].
  rewrite Hpref.
  rewrite <- Hp.
  unfold flush_spaces_z.
  destruct (Z.eqb_spec p 0); try lia.
  destruct (Z.eqb_spec p 1); try lia.
  destruct (Z.eqb_spec p 2); try lia.
  split; [rewrite <- app_assoc; reflexivity | exact Hpend].
Qed.

Lemma fix_spaces_output_pending0 : forall s,
  fix_spaces_pending_z (Zlength s) s = 0 ->
  fix_spaces_output_z s = fix_spaces_prefix_z (Zlength s) s.
Proof.
  intros s Hpending.
  unfold fix_spaces_output_z.
  rewrite Hpending.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma fix_spaces_output_pending1 : forall s,
  fix_spaces_pending_z (Zlength s) s = 1 ->
  fix_spaces_output_z s = fix_spaces_prefix_z (Zlength s) s ++ [95].
Proof.
  intros s Hpending.
  unfold fix_spaces_output_z.
  rewrite Hpending.
  reflexivity.
Qed.

Lemma fix_spaces_output_pending2 : forall s,
  fix_spaces_pending_z (Zlength s) s = 2 ->
  fix_spaces_output_z s = fix_spaces_prefix_z (Zlength s) s ++ [95; 95].
Proof.
  intros s Hpending.
  unfold fix_spaces_output_z.
  rewrite Hpending.
  simpl.
  reflexivity.
Qed.

Lemma fix_spaces_output_pending_more : forall s p,
  p = fix_spaces_pending_z (Zlength s) s ->
  p > 2 ->
  fix_spaces_output_z s = fix_spaces_prefix_z (Zlength s) s ++ [45].
Proof.
  intros s p Hp Hmore.
  unfold fix_spaces_output_z.
  rewrite <- Hp.
  unfold flush_spaces_z.
  destruct (Z.eqb_spec p 0); try lia.
  destruct (Z.eqb_spec p 1); try lia.
  destruct (Z.eqb_spec p 2); try lia.
  reflexivity.
Qed.

Lemma ascii_of_z_space_iff : forall c,
  0 <= c < 256 ->
  ascii_of_z c = space <-> c = 32.
Proof.
  intros c Hrange.
  split; intros H.
  - apply (f_equal nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by lia.
    vm_compute in H.
    change 32%nat with (Z.to_nat 32) in H.
    apply Z2Nat.inj in H; lia.
  - subst c. reflexivity.
Qed.

Lemma string_of_list_z_flush_spaces : forall n,
  0 <= n ->
  string_of_list_z (flush_spaces_z n) =
  string_of_list_ascii (flush_spaces (Z.to_nat n)).
Proof.
  intros n Hn.
  unfold flush_spaces_z, flush_spaces.
  destruct (Z.eqb_spec n 0); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 1); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 2); subst; simpl; [reflexivity |].
  destruct (Z.to_nat n) as [| [| [| m]]] eqn:Hnat; try lia.
  reflexivity.
Qed.

Lemma string_of_list_z_app_140 : forall a b,
  string_of_list_z (a ++ b) =
  (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_of_list_ascii_app_140 : forall a b,
  string_of_list_ascii (a ++ b) =
  (string_of_list_ascii a ++ string_of_list_ascii b)%string.
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_append_assoc_140 : forall a b c,
  ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a as [| ch rest IH]; intros b c; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma fix_spaces_scan_z_correct_aux : forall s out pending,
  ascii_range_z s ->
  0 <= pending ->
  string_of_list_z
    (fst (fold_left scan_step_z s (out, pending)) ++
     flush_spaces_z (snd (fold_left scan_step_z s (out, pending)))) =
  (string_of_list_z out ++
   string_of_list_ascii (fix_spaces_scan (map ascii_of_z s) (Z.to_nat pending)))%string.
Proof.
  induction s as [| c rest IH]; intros out pending Hrange Hpending.
  - simpl.
    rewrite string_of_list_z_app_140.
    rewrite string_of_list_z_flush_spaces by lia.
    reflexivity.
  - simpl map.
    assert (Hc_range : 0 <= c < 256).
    {
      specialize (Hrange 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia)).
      change (Znth 0 (c :: rest) 0) with c in Hrange.
      lia.
    }
    assert (Hrest_range : ascii_range_z rest).
    {
      intros i Hi.
      specialize (Hrange (i + 1)).
      replace (Znth i rest 0) with (Znth (i + 1) (c :: rest) 0).
      - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg rest); lia.
      - unfold Znth. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    destruct (Z.eq_dec c 32) as [Hspace | Hnonspace].
    + subst c.
      replace (ascii_of_z 32) with space by reflexivity.
      destruct (Ascii.ascii_dec space space) as [_ | Hbad]; [| contradiction].
      simpl.
      rewrite IH by (assumption || lia).
      replace (S (Z.to_nat pending)) with (Z.to_nat (pending + 1)) by lia.
      reflexivity.
    + assert (Hascii_nonspace : ascii_of_z c <> space).
      { intro Hbad. apply ascii_of_z_space_iff in Hbad; lia. }
      destruct (Ascii.ascii_dec (ascii_of_z c) space) as [Hbad | _].
      { contradiction. }
      simpl.
      replace (c =? 32) with false by (symmetry; apply Z.eqb_neq; exact Hnonspace).
      rewrite IH by (assumption || lia).
      rewrite !string_of_list_z_app_140.
      rewrite string_of_list_z_flush_spaces by lia.
      destruct (Ascii.ascii_dec (ascii_of_z c) space) as [Hbad2 | _];
        [contradiction |].
      destruct (Z.to_nat pending) as [| [| [| m]]] eqn:Hpn; simpl;
        rewrite ?string_append_assoc_140; reflexivity.
Qed.

Lemma fix_spaces_scan_z_correct : forall s,
  ascii_range_z s ->
  string_of_list_z (fix_spaces_output_z s) =
  string_of_list_ascii (fix_spaces_scan (map ascii_of_z s) 0).
Proof.
  intros s Hrange.
  unfold fix_spaces_output_z, fix_spaces_prefix_z, fix_spaces_pending_z,
         fix_spaces_state_z.
  rewrite z_to_nat_Zlength, firstn_all.
  change 0%nat with (Z.to_nat 0).
  rewrite fix_spaces_scan_z_correct_aux by (assumption || lia).
  reflexivity.
Qed.

Lemma problem_140_spec_z_intro : forall input output,
  ascii_range_z input ->
  output = fix_spaces_output_z input ->
  problem_140_spec_z input output.
Proof.
  intros input output Hrange Hout.
  unfold problem_140_spec_z, problem_140_spec, fix_spaces.
  rewrite Hout.
  rewrite list_ascii_of_string_string_of_list_z.
  rewrite fix_spaces_scan_z_correct by assumption.
  reflexivity.
Qed.
