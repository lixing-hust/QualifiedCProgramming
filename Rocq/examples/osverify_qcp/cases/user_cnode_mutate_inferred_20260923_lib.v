(* Independent implementation-derived specification, 2026-09-23.
   Sequential ordinary memory only; critical markers are projection identities.
   No OS capability-policy or original interrupt-primitive correctness claim. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import SimpleC.SL.SeparationLogic.
Import ListNotations.
Local Open Scope Z_scope.

(* A finite sparse footprint, with optional values for write-only storage.
   This is a memory description, not an executable copy of the C algorithm. *)
Inductive mu_kind := MUword | MUptr | MUbyte.
Record mu_cell := MuCell {
  mu_address : Z;
  mu_cell_kind : mu_kind;
  mu_initial : option Z
}.
Record mu_layout := MuLayout {
  mu_table_base : Z; mu_parent_base : Z; mu_tcb_global : Z;
  mu_tcb_field : Z -> Z;
  mu_slot_field : Z -> Z -> Z;
  mu_type_field : Z -> Z -> Z;
  mu_content_field : Z -> Z -> Z;
  mu_right_field : Z -> Z -> Z
}.
Record mu_state := MuState { mu_layout_of : mu_layout; mu_cells : list mu_cell }.
Definition mu_cell_list := list mu_cell.
Definition mu_kind_eqb (a b : mu_kind) : bool :=
  match a,b with
  | MUword,MUword | MUptr,MUptr | MUbyte,MUbyte => true
  | _,_ => false
  end.
Fixpoint mu_find_cells (h : mu_cell_list) (k : mu_kind) (a : Z) : option (option Z) :=
  match h with
  | [] => None
  | c::tl => if (Z.eqb (mu_address c) a && mu_kind_eqb (mu_cell_kind c) k)%bool
             then Some (mu_initial c) else mu_find_cells tl k a
  end.
Definition mu_distinct h := NoDup (map mu_address (mu_cells h)).
Definition mu_find h k a := mu_find_cells (mu_cells h) k a.
Definition mu_readable h k a : Prop := exists v, mu_find h k a = Some (Some v).
Definition mu_writable h k a : Prop := exists v, mu_find h k a = Some v.
Definition mu_value h k a : Z :=
  match mu_find h k a with Some (Some v) => v | _ => 0 end.
Definition mu_cell_heap (c : mu_cell) : naive_C_Rules.expr :=
  match mu_cell_kind c, mu_initial c with
  | MUword,Some v => naive_C_Rules.store_uint (mu_address c) v
  | MUword,None => naive_C_Rules.undef_store_uint (mu_address c)
  | MUptr,Some v => naive_C_Rules.store_ptr (mu_address c) v
  | MUptr,None => naive_C_Rules.undef_store_ptr (mu_address c)
  | MUbyte,Some v => naive_C_Rules.store_uchar (mu_address c) v
  | MUbyte,None => naive_C_Rules.undef_store_uchar (mu_address c)
  end.
Fixpoint mu_cells_heap (h : mu_cell_list) : naive_C_Rules.expr :=
  match h with [] => naive_C_Rules.emp
  | c::tl => naive_C_Rules.sepcon (mu_cell_heap c) (mu_cells_heap tl)
  end.

Definition mu_heap h := mu_cells_heap (mu_cells h).
Definition mu_table_addr h i := mu_table_base (mu_layout_of h) + i * naive_C_Rules.ptr_size_Z.
Definition mu_parent_addr h i := mu_parent_base (mu_layout_of h) + i.
Definition mu_tcb_prio h p := mu_tcb_field (mu_layout_of h) p.
Definition mu_slot_addr h p f := mu_slot_field (mu_layout_of h) p f.
Definition mu_type_addr h p f := mu_type_field (mu_layout_of h) p f.
Definition mu_content_addr h p f := mu_content_field (mu_layout_of h) p f.
Definition mu_right_addr h p f := mu_right_field (mu_layout_of h) p f.
Definition mu_tb h := mu_table_base (mu_layout_of h).
Definition mu_pb h := mu_parent_base (mu_layout_of h).
Definition mu_cg h := mu_tcb_global (mu_layout_of h).

(* Generic finite-memory resource lenses. No program-specific transition rules. *)
Definition mu_matches k a c := (Z.eqb (mu_address c) a && mu_kind_eqb (mu_cell_kind c) k)%bool.
Definition mu_without h k a := MuState (mu_layout_of h)
  (filter (fun c => negb (mu_matches k a c)) (mu_cells h)).
Definition mu_set h k a v := MuState (mu_layout_of h)
  (map (fun c => if mu_matches k a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) (mu_cells h)).
Definition mu_land := Z.land.

Definition mu_space h i := mu_value h MUptr (mu_table_addr h i).
Definition mu_type h p f := mu_value h MUword (mu_type_addr h p f).
Definition mu_right h p f := mu_value h MUword (mu_right_addr h p f).
Definition mu_content h p f := mu_value h MUword (mu_content_addr h p f).
Definition mu_u8 z := 0 <= z <= 255.
Definition mu_u32 z := 0 <= z <= 4294967295.
Definition mu_complement z := Z.lxor z 4294967295.
Definition mu_strict_subrights old requested : Prop :=
  Z.land (mu_complement old) requested = 0 /\ old <> requested.
Definition mu_core_indices d s f : Prop := 0 <= f <= 16 /\ 0 <= d < 64 /\ 0 <= s < 64.
Definition mu_user_indices d s : Prop := 0 <= d < 63 /\ 0 <= s < 63.
Definition mu_core_success h d s f rights : Prop :=
  mu_core_indices d s f /\ mu_space h d <> 0 /\ mu_space h s <> 0 /\
  mu_type h (mu_space h s) f = 1 /\
  mu_strict_subrights (mu_right h (mu_space h s) f) rights.

(* Read provenance is checked at the actual read point. In particular the
   content read follows the destination type store; no whole-object disjointness
   assumption may be used to demand an unnecessarily initialized old cell. *)
Definition mu_core_safe h d s f rights : Prop :=
  mu_u8 d /\ mu_u8 s /\ mu_u32 f /\ mu_u32 rights /\
  (mu_core_indices d s f ->
    mu_readable h MUptr (mu_table_addr h d) /\ mu_readable h MUptr (mu_table_addr h s) /\
    (mu_space h d <> 0 /\ mu_space h s <> 0 ->
      mu_readable h MUword (mu_type_addr h (mu_space h s) f) /\
      (mu_type h (mu_space h s) f = 1 ->
        mu_readable h MUword (mu_right_addr h (mu_space h s) f)) /\
      (mu_core_success h d s f rights ->
        mu_readable
          (mu_set h MUword (mu_type_addr h (mu_space h d) f) 1)
          MUword (mu_content_addr h (mu_space h s) f) /\
        mu_writable h MUword (mu_type_addr h (mu_space h d) f) /\
        mu_writable h MUword (mu_content_addr h (mu_space h d) f) /\
        mu_writable h MUword (mu_right_addr h (mu_space h d) f) /\
        mu_writable h MUword (mu_slot_addr h (mu_space h s) f)))).

(* Closed read-provenance equations. They select the last earlier writer to
   a physical address, including CROSS-FIELD aliases, without excluding layouts
   or defining an executable C control-flow mirror. *)
Definition mu_copied_content h d s f : Z :=
  if Z.eqb (mu_content_addr h (mu_space h s) f)
           (mu_type_addr h (mu_space h d) f)
  then 1 else mu_content h (mu_space h s) f.
Definition mu_right_before_clear h d s f rights : Z :=
  let a := mu_right_addr h (mu_space h s) f in
  let dp := mu_space h d in
  if Z.eqb a (mu_right_addr h dp f) then rights else
  if Z.eqb a (mu_content_addr h dp f) then mu_copied_content h d s f else
  if Z.eqb a (mu_type_addr h dp f) then 1 else
  mu_right h (mu_space h s) f.

(* Final state is the value of the last write to each physical word. This
   specializes to the original same-slot/disjoint-slot result on that domain,
   and also covers word-field overlaps between different CSPACE bases. *)
Definition mu_final_word h d s f rights a : option Z :=
  let dp := mu_space h d in let sp := mu_space h s in
  if Z.eqb a (mu_slot_addr h sp f) then Some 0 else
  if Z.eqb a (mu_right_addr h sp f) then
    Some (Z.land (mu_right_before_clear h d s f rights) (mu_complement rights)) else
  if Z.eqb a (mu_right_addr h dp f) then Some rights else
  if Z.eqb a (mu_content_addr h dp f) then Some (mu_copied_content h d s f) else
  if Z.eqb a (mu_type_addr h dp f) then Some 1 else
  match mu_find h MUword a with Some v => v | None => None end.
Definition mu_final_cell h d s f rights c :=
  match mu_cell_kind c with
  | MUword => MuCell (mu_address c) MUword (mu_final_word h d s f rights (mu_address c))
  | _ => c
  end.
Definition mu_success_state h d s f rights := MuState (mu_layout_of h) (map (mu_final_cell h d s f rights) (mu_cells h)).
Definition mu_core_result h h' d s f rights ret : Prop :=
  (mu_core_success h d s f rights /\ ret = 0 /\ h' = mu_success_state h d s f rights) \/
  (~ mu_core_success h d s f rights /\ ret = 8 /\ h' = h).

Definition mu_current_tcb h := mu_value h MUptr (mu_cg h).
Definition mu_current_prio h := mu_value h MUbyte (mu_tcb_prio h (mu_current_tcb h)).
Definition mu_current_space h := mu_space h (mu_current_prio h).
Definition mu_authorized h d s : Prop :=
  Z.land (mu_right h (mu_current_space h) 11) 8 <> 0 /\
  mu_value h MUbyte (mu_parent_addr h d) = s.
Definition mu_user_safe h d s f rights : Prop :=
  mu_u8 d /\ mu_u8 s /\ mu_u32 f /\ mu_u32 rights /\
  (mu_user_indices d s ->
    mu_readable h MUptr (mu_cg h) /\ mu_current_tcb h <> 0 /\
    mu_readable h MUbyte (mu_tcb_prio h (mu_current_tcb h)) /\
    0 <= mu_current_prio h < 64 /\
    mu_readable h MUptr (mu_table_addr h (mu_current_prio h)) /\
    (mu_current_space h <> 0 ->
      mu_readable h MUword (mu_right_addr h (mu_current_space h) 11) /\
      (Z.land (mu_right h (mu_current_space h) 11) 8 <> 0 ->
        mu_readable h MUbyte (mu_parent_addr h d)) /\
      (mu_authorized h d s -> mu_core_safe h d s f rights))).
Definition mu_user_result h h' d s f rights ret : Prop :=
  (~ mu_user_indices d s /\ ret = 42 /\ h' = h) \/
  (mu_user_indices d s /\ mu_current_space h = 0 /\ ret = 8 /\ h' = h) \/
  (mu_user_indices d s /\ mu_current_space h <> 0 /\ ~ mu_authorized h d s /\ ret = 252 /\ h' = h) \/
  (mu_user_indices d s /\ mu_current_space h <> 0 /\ mu_authorized h d s /\
    mu_core_result h h' d s f rights ret).

Require Import Coq.micromega.Lia.
Lemma mu_find_set__success_state : forall h a b v,
 mu_find (mu_set h MUword b v) MUword a =
 if Z.eqb a b then
   match mu_find h MUword a with Some _ => Some (Some v) | None => None end
 else mu_find h MUword a.
Proof.
 intros [l cs] a b v; unfold mu_find, mu_set; simpl.
 induction cs as [|[x k ov] tl IH]; simpl; [destruct (a =? b); reflexivity|].
 unfold mu_matches in *; simpl in *.
 destruct k; simpl; rewrite ?Bool.andb_false_r; simpl; try (rewrite IH; reflexivity).
 destruct (x =? b) eqn:E1; destruct (x =? a) eqn:E2; destruct (a =? b) eqn:E3;
 simpl; rewrite ?E2, ?IH, ?E3; simpl; try reflexivity;
 apply Z.eqb_eq in E1 || apply Z.eqb_neq in E1;
 apply Z.eqb_eq in E2 || apply Z.eqb_neq in E2;
 apply Z.eqb_eq in E3 || apply Z.eqb_neq in E3;
 congruence.
Qed.
Lemma mu_value_set__success_state : forall h a b v,
 mu_writable h MUword b ->
 mu_value (mu_set h MUword b v) MUword a =
 if Z.eqb a b then v else mu_value h MUword a.
Proof.
 intros h a b v [ov H]; unfold mu_value; rewrite mu_find_set__success_state.
 destruct (Z.eqb_spec a b); [subst; rewrite H|]; reflexivity.
Qed.
Lemma mu_find_member__success_state : forall cs c,
 NoDup (map mu_address cs) -> In c cs ->
 mu_find_cells cs (mu_cell_kind c) (mu_address c) = Some (mu_initial c).
Proof.
 induction cs as [|x xs IH]; intros c ND IN; [contradiction|].
 inversion ND as [|a aa NIN ND']; subst. simpl in IN.
 destruct IN as [<-|IN].
 - simpl; rewrite Z.eqb_refl; destruct (mu_cell_kind x); reflexivity.
 - simpl. destruct (Z.eqb_spec (mu_address x) (mu_address c)) as [E|E].
   + exfalso; apply NIN; rewrite E; apply in_map; exact IN.
   + simpl; apply IH; assumption.
Qed.
Lemma mu_five_writes_final__success_state : forall h d s f rights,
 let ta := mu_type_addr h (mu_space h d) f in
 let ca := mu_content_addr h (mu_space h d) f in
 let ra := mu_right_addr h (mu_space h d) f in
 let sc := mu_content_addr h (mu_space h s) f in
 let sr := mu_right_addr h (mu_space h s) f in
 let ss := mu_slot_addr h (mu_space h s) f in
 let h1 := mu_set h MUword ta 1 in
 let cv := mu_value h1 MUword sc in
 let h2 := mu_set h1 MUword ca cv in
 let h3 := mu_set h2 MUword ra rights in
 mu_distinct h -> mu_writable h MUword ta ->
 mu_writable h1 MUword ca -> mu_writable h2 MUword ra ->
 mu_set (mu_set h3 MUword sr
   (mu_land (mu_value h3 MUword sr) (mu_complement rights))) MUword ss 0 =
 mu_success_state h d s f rights.
Proof.
 intros h d s f rights ta ca ra sc sr ss h1 cv h2 h3 ND WT WC WR.
 assert (EC : cv = mu_copied_content h d s f).
 { unfold cv, h1; rewrite mu_value_set__success_state by exact WT.
   reflexivity. }
 assert (ER : mu_value h3 MUword sr = mu_right_before_clear h d s f rights).
 { unfold h3; rewrite mu_value_set__success_state by exact WR.
   unfold h2; rewrite mu_value_set__success_state by exact WC.
   unfold h1; rewrite mu_value_set__success_state by exact WT.
   rewrite EC; reflexivity. }
 rewrite ER. unfold h3, h2, h1. rewrite EC.
 unfold mu_set, mu_success_state; simpl; repeat rewrite map_map.
 f_equal. apply map_ext_in. intros [a k ov] IN.
 pose proof (mu_find_member__success_state (mu_cells h) (MuCell a k ov) ND IN) as LOOK.
 unfold mu_final_cell, mu_final_word, mu_matches; simpl in *.
 destruct k; simpl; rewrite ?Bool.andb_false_r; simpl; try reflexivity.
 unfold mu_find; rewrite LOOK.
 fold ta ca ra sr ss.
 destruct (a =? ta); simpl; destruct (a =? ca); simpl; destruct (a =? ra);
 simpl; destruct (a =? sr); simpl; destruct (a =? ss); reflexivity.
Qed.
Lemma mu_mask_guard__success_state : forall old r,
 0 <= r <= 4294967295 ->
 Z.land (Z.lnot old) r = Z.land (mu_complement old) r.
Proof.
 intros old r R. apply Z.bits_inj'; intros n N.
 unfold mu_complement; rewrite !Z.land_spec, Z.lnot_spec, Z.lxor_spec by lia.
 destruct (Z_lt_ge_dec n 32) as [LO|HI].
 - change 4294967295 with (Z.ones 32).
   rewrite Z.ones_spec_low by lia. destruct (Z.testbit old n); reflexivity.
 - assert (B : Z.testbit r n = false).
   { replace r with (r mod 2^32) by (rewrite Z.mod_small; [reflexivity|lia]).
     apply Z.mod_pow2_bits_high; lia. }
   rewrite B; repeat rewrite Bool.andb_false_r; reflexivity.
Qed.
Lemma mu_mask_guard__rights_rejection : forall old requested,
  mu_u32 requested ->
  Z.land (Z.lnot old) requested = Z.land (mu_complement old) requested.
Proof.
  intros old requested Hr.
  assert (Hm : Z.land requested 4294967295 = requested).
  { change (Z.land requested (Z.ones 32) = requested).
    rewrite Z.land_ones by lia.
    apply Z.mod_small. unfold mu_u32 in Hr. change (0 <= requested < 4294967296). lia. }
  apply Z.bits_inj. intros n.
  destruct (Z_lt_ge_dec n 0) as [Hn|Hn].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - pose proof (f_equal (fun z => Z.testbit z n) Hm) as Hb.
    cbn beta in Hb. rewrite Z.land_spec in Hb.
    unfold mu_complement. rewrite !Z.land_spec, Z.lnot_spec, Z.lxor_spec by lia.
    destruct (Z.testbit old n), (Z.testbit requested n),
      (Z.testbit 4294967295 n); simpl in *; congruence.
Qed.
Lemma mu_mask_guard__destination_initial_safety old r :
 mu_u32 r -> Z.land (mu_complement old) r = Z.land (Z.lnot old) r.
Proof.
 intros Hr. unfold mu_u32 in Hr. unfold mu_complement.
 apply Z.bits_inj'; intros n Hn.
 rewrite !Z.land_spec, Z.lxor_spec, Z.lnot_spec by lia.
 destruct (Z_lt_ge_dec n 32).
 - replace 4294967295 with (Z.ones 32) by reflexivity.
   rewrite Z.ones_spec_low by lia.
   destruct (Z.testbit old n), (Z.testbit r n); reflexivity.
 - assert (Hmod : r mod 2^32 = r) by (apply Z.mod_small; cbn; lia).
   assert (Hb : Z.testbit r n = false).
   { rewrite <- Hmod. apply Z.mod_pow2_bits_high. lia. }
   rewrite Hb. now rewrite !Bool.andb_false_r.
Qed.
Lemma mu_writable_set__destination_initial_safety h k a k2 a2 v :
 mu_writable h k a -> mu_writable (mu_set h k2 a2 v) k a.
Proof.
 destruct h as [l cs]. unfold mu_writable, mu_find, mu_set; cbn.
 induction cs as [|[ca ck ci] tl IH]; cbn; intros [x Hx].
 - discriminate.
 - unfold mu_matches; cbn.
   destruct (Z.eqb ca a2 && mu_kind_eqb ck k2)%bool; cbn;
   destruct (Z.eqb ca a && mu_kind_eqb ck k)%bool eqn:E; cbn in *.
   + exists (Some v). reflexivity.
   + apply IH. eauto.
   + eauto.
   + apply IH. eauto.
Qed.
Lemma mu_mask_guard__destination_right_safety : forall a b,
  mu_u32 b -> Z.land (Z.lnot a) b = 0 ->
  Z.land (mu_complement a) b = 0.
Proof.
  intros a b Hb Hguard.
  assert (Hmask : Z.land b 4294967295 = b).
  { change (Z.land b (Z.ones 32) = b).
    rewrite Z.land_ones by lia.
    apply Z.mod_small. unfold mu_u32 in Hb. cbn; lia. }
  apply Z.bits_inj. intros i.
  pose proof (f_equal (fun z => Z.testbit z i) Hguard) as Hg.
  pose proof (f_equal (fun z => Z.testbit z i) Hmask) as Hm.
  cbn beta in Hg, Hm.
  destruct (Z_lt_ge_dec i 0) as [Hi|Hi].
  { repeat rewrite Z.testbit_neg_r by lia. reflexivity. }
  unfold mu_complement. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  rewrite Z.land_spec, Z.lnot_spec, Z.bits_0 in Hg by lia.
  rewrite Z.land_spec in Hm.
  destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit 4294967295 i); cbn in *; congruence.
Qed.
Lemma mu_writable_set__destination_right_safety : forall h k a v k' a',
 mu_writable h k' a' -> mu_writable (mu_set h k a v) k' a'.
Proof.
 intros [l cs] k a v k' a'. unfold mu_writable, mu_find, mu_set; cbn.
 induction cs as [|[ca ck cv] tl IH]; cbn; intros [w Hw].
 - discriminate.
 - unfold mu_matches; cbn.
   destruct ((ca =? a) && mu_kind_eqb ck k)%bool; cbn;
   destruct ((ca =? a') && mu_kind_eqb ck k')%bool eqn:E; cbn in *.
   + eexists; reflexivity.
   + apply IH. eauto.
   + eexists; reflexivity.
   + apply IH. eauto.
Qed.
Lemma mu_readable_set__source_right_safety h k a v kr ar :
  mu_readable h kr ar -> mu_readable (mu_set h k a v) kr ar.
Proof.
  destruct h as [layout cells].
  unfold mu_readable, mu_find, mu_set; simpl.
  induction cells as [|[ca ck cv] tl IH]; simpl.
  - intros [w H]; discriminate.
  - unfold mu_matches; simpl.
    destruct (Z.eqb ca a && mu_kind_eqb ck k)%bool eqn:E; simpl;
    destruct (Z.eqb ca ar && mu_kind_eqb ck kr)%bool eqn:F; simpl.
    + intros _. exists v. reflexivity.
    + exact IH.
    + intros H. exact H.
    + exact IH.
Qed.
Lemma mu_high_bits__clear_mask a n :
  0 <= a < 2^32 -> 32 <= n -> Z.testbit a n = false.
Proof.
  intros Ha Hn. destruct (Z.eq_dec a 0) as [->|Hnz].
  - apply Z.bits_0.
  - apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 a 32 ltac:(lia)) (proj2 Ha)). lia.
Qed.
Lemma mu_clear_mask_bounded_result__clear_mask x r :
  0 <= r < 2^32 -> 0 <= Z.land x (Z.lnot r) < 2^32 ->
  Z.land x (Z.lnot r) = Z.land x (Z.lxor r (2^32-1)).
Proof.
  intros Hr Hy. apply Z.bits_inj. intro n.
  destruct (Z_lt_ge_dec n 0) as [Hneg|Hnonneg].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z_lt_ge_dec n 32) as [Hlow|Hhigh].
    + rewrite !Z.land_spec, Z.lnot_spec by lia.
      rewrite Z.lxor_spec.
      change (Z.testbit (2^32-1) n) with (Z.testbit (Z.ones 32) n).
      rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit x n), (Z.testbit r n); reflexivity.
    + rewrite (mu_high_bits__clear_mask _ n Hy ltac:(lia)).
      rewrite Z.land_spec, Z.lxor_spec.
      rewrite (mu_high_bits__clear_mask _ n Hr ltac:(lia)).
      change (Z.testbit (2^32-1) n) with (Z.testbit (Z.ones 32) n).
      rewrite Z.ones_spec_high by lia.
      destruct (Z.testbit x n); reflexivity.
Qed.
Lemma mu_mask_guard__source_slot_safety old r :
  0 <= r <= 4294967295 -> Z.land (Z.lnot old) r = 0 ->
  Z.land (mu_complement old) r = 0.
Proof.
  intros Hr Hguard.
  assert (Hm : Z.land r 4294967295 = r).
  { change (Z.land r (Z.ones 32) = r).
    rewrite Z.land_ones by lia. apply Z.mod_small. cbn; lia. }
  apply Z.bits_inj. intros n.
  destruct (Z_lt_ge_dec n 0) as [Hn|Hn].
  - repeat rewrite Z.testbit_neg_r by lia. reflexivity.
  - pose proof (f_equal (fun x => Z.testbit x n) Hguard) as Hg.
    pose proof (f_equal (fun x => Z.testbit x n) Hm) as Hb.
    cbn beta in Hg, Hb.
    unfold mu_complement. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    rewrite Z.land_spec, Z.lnot_spec, Z.bits_0 in Hg by lia.
    rewrite Z.land_spec in Hb.
    destruct (Z.testbit old n), (Z.testbit r n), (Z.testbit 4294967295 n); simpl in *; congruence.
Qed.
Lemma mu_writable_set__source_slot_safety h k a v k' a' :
  mu_writable h k' a' -> mu_writable (mu_set h k a v) k' a'.
Proof.
  destruct h as [l cells]. unfold mu_writable, mu_find, mu_set; simpl.
  induction cells as [|[ca ck cv] tl IH]; simpl; intros [w Hw].
  - discriminate.
  - unfold mu_matches; simpl.
    destruct (Z.eqb ca a && mu_kind_eqb ck k)%bool eqn:Hu; simpl;
      destruct (Z.eqb ca a' && mu_kind_eqb ck k')%bool eqn:Hq; simpl in *.
    + eexists; reflexivity.
    + apply IH. eexists; exact Hw.
    + eexists; reflexivity.
    + apply IH. eexists; exact Hw.
Qed.
Lemma mu_filter_absent__pointer_lenses : forall cs a,
 ~ In a (map mu_address cs) ->
 filter (fun c => negb (mu_matches MUptr a c)) cs = cs.
Proof.
 induction cs as [|c cs IH]; intros a H; simpl; auto.
 assert (Ha : mu_address c <> a) by (intro E; apply H; simpl; auto).
 assert (Eb : Z.eqb (mu_address c) a = false) by (apply Z.eqb_neq; exact Ha).
 unfold mu_matches at 1. rewrite Eb.
 simpl. f_equal. apply IH. intro Hi. apply H. simpl; auto.
Qed.
Lemma mu_ptr_cells__pointer_lenses : forall cs a v,
 NoDup (map mu_address cs) -> mu_find_cells cs MUptr a = Some (Some v) ->
 (naive_C_Rules.derivable1 (mu_cells_heap cs)
   (naive_C_Rules.sepcon (naive_C_Rules.store_ptr a v)
     (mu_cells_heap (filter (fun c => negb (mu_matches MUptr a c)) cs)))) /\
 (naive_C_Rules.derivable1
   (naive_C_Rules.sepcon (naive_C_Rules.store_ptr a v)
     (mu_cells_heap (filter (fun c => negb (mu_matches MUptr a c)) cs)))
   (mu_cells_heap cs)).
Proof.
 Import naive_C_Rules.
 Local Open Scope sac.
 induction cs as [|[b k ov] cs IH]; intros a v Hnd Hfind; simpl in Hfind; try discriminate.
 inversion Hnd as [|? ? Hnot Htail]; subst.
 destruct (Z.eqb b a && mu_kind_eqb k MUptr)%bool eqn:E.
 - apply Bool.andb_true_iff in E. destruct E as [Eb Ek].
   apply Z.eqb_eq in Eb. subst b. destruct k; simpl in Ek; try discriminate.
   inversion Hfind; subst ov.
   simpl.
   rewrite !mu_filter_absent__pointer_lenses by exact Hnot.
   unfold mu_matches; simpl. rewrite Z.eqb_refl. simpl.
   unfold mu_cell_heap; simpl. split; cancel.
 - specialize (IH a v Htail Hfind). destruct IH as [Hex Hback].
   change (mu_matches MUptr a {| mu_address := b; mu_cell_kind := k; mu_initial := ov |} = false) in E.
   simpl mu_cells_heap. simpl filter. rewrite E. simpl negb.
   simpl mu_cells_heap.
   split.
   + sep_apply Hex. cancel.
   + sep_apply Hback. cancel.
Qed.
Lemma mu_ptr_lens__pointer_lenses : forall h a,
 mu_distinct h -> mu_readable h MUptr a ->
 (naive_C_Rules.derivable1 (mu_heap h)
   (naive_C_Rules.sepcon (naive_C_Rules.store_ptr a (mu_value h MUptr a))
     (mu_heap (mu_without h MUptr a)))) /\
 (naive_C_Rules.derivable1
   (naive_C_Rules.sepcon (naive_C_Rules.store_ptr a (mu_value h MUptr a))
     (mu_heap (mu_without h MUptr a))) (mu_heap h)).
Proof.
 intros h a Hd [v Hv]. unfold mu_value. rewrite Hv.
 unfold mu_heap, mu_without; simpl.
 apply mu_ptr_cells__pointer_lenses; assumption.
Qed.
Lemma mu_filter_absent__byte_lenses : forall cs a,
 ~ In a (map mu_address cs) ->
 filter (fun c => negb (mu_matches MUbyte a c)) cs = cs.
Proof.
 intros cs; induction cs as [|c cs IH]; intros a H; simpl; auto.
 assert (Ha : mu_address c <> a) by (intro E; apply H; left; exact E).
 unfold mu_matches at 1. rewrite (proj2 (Z.eqb_neq _ _) Ha). simpl.
 f_equal. apply IH. intro HIn. apply H. right. exact HIn.
Qed.
Lemma mu_byte_cells_lens__byte_lenses : forall cs a v,
 NoDup (map mu_address cs) -> mu_find_cells cs MUbyte a = Some (Some v) ->
 (naive_C_Rules.derivable1 (mu_cells_heap cs) (naive_C_Rules.sepcon (naive_C_Rules.store_uchar a v) (mu_cells_heap (filter (fun c => negb (mu_matches MUbyte a c)) cs)))) /\
 (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uchar a v) (mu_cells_heap (filter (fun c => negb (mu_matches MUbyte a c)) cs))) (mu_cells_heap cs)).
Proof.
 Import naive_C_Rules.
 intros cs; induction cs as [|[b k ov] cs IH]; intros a v Hnd Hfind; simpl in Hfind; try discriminate.
 inversion Hnd as [|? ? Hnot Htail]; subst.
 destruct (Z.eqb b a && mu_kind_eqb k MUbyte)%bool eqn:E.
 - apply Bool.andb_true_iff in E. destruct E as [Eb Ek]. apply Z.eqb_eq in Eb. subst b.
   destruct k; simpl in Ek; try discriminate. inversion Hfind; subst ov.
   cbn [mu_cells_heap mu_cell_heap filter mu_matches mu_address mu_cell_kind mu_initial mu_kind_eqb].
   assert (Em : mu_matches MUbyte a (MuCell a MUbyte (Some v)) = true) by (unfold mu_matches; simpl; rewrite Z.eqb_refl; reflexivity). rewrite Em. simpl.
   rewrite mu_filter_absent__byte_lenses by exact Hnot.
   split; cancel; try (intros m H; exact H).
 - specialize (IH a v Htail Hfind). destruct IH as [Hex Hre].
   change (mu_matches MUbyte a (MuCell b k ov) = false) in E.
   cbn [mu_cells_heap filter]. rewrite E. simpl.
   split.
   + sep_apply_l_atomic Hex. cancel; try (intros m H; exact H).
   + sep_apply_r_atomic Hre. cancel; try (intros m H; exact H).
Qed.
Lemma mu_byte_lens__byte_lenses : forall h a,
 mu_distinct h -> mu_readable h MUbyte a ->
 (naive_C_Rules.derivable1 (mu_heap h) (naive_C_Rules.sepcon (naive_C_Rules.store_uchar a (mu_value h MUbyte a)) (mu_heap (mu_without h MUbyte a)))) /\
 (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uchar a (mu_value h MUbyte a)) (mu_heap (mu_without h MUbyte a))) (mu_heap h)).
Proof.
 intros h a Hd [v Hv]. unfold mu_value. rewrite Hv.
 apply mu_byte_cells_lens__byte_lenses; assumption.
Qed.
Lemma mu_filter_absent__source_word_lenses : forall l a,
  ~ In a (map mu_address l) ->
  filter (fun c => negb (mu_matches MUword a c)) l = l.
Proof.
  induction l as [|c l IH]; intros a H; simpl; auto.
  assert (E: Z.eqb (mu_address c) a = false).
  { apply Z.eqb_neq. intro E; apply H; simpl; auto. }
  unfold mu_matches at 1; rewrite E; simpl.
  f_equal; apply IH; intro K; apply H; simpl; auto.
Qed.
Lemma mu_list_word_lens__source_word_lenses : forall l a v,
  NoDup (map mu_address l) -> mu_find_cells l MUword a = Some (Some v) ->
  (naive_C_Rules.derivable1 (mu_cells_heap l)
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v)
      (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) l)))) /\
  (naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v)
      (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) l)))
    (mu_cells_heap l)).
Proof.
  Import naive_C_Rules.
  induction l as [|[b k w] l IH]; intros a v ND F; simpl in F; try discriminate.
  inversion ND as [|? ? Hnot ND']; subst.
  destruct (Z.eqb b a) eqn:E; destruct k; simpl in F.
  - apply Z.eqb_eq in E; subst b. inversion F; subst w.
    simpl. unfold mu_matches; simpl. rewrite Z.eqb_refl; simpl.
    pose proof (mu_filter_absent__source_word_lenses l a Hnot) as HF.
    unfold mu_matches in HF; rewrite HF.
    split; cancel.
    all: try reflexivity.

  - simpl. unfold mu_matches; simpl. rewrite E; simpl.
    destruct (IH a v ND' F) as [L R]. unfold mu_matches in L, R. split.
    + sep_apply_l_atomic L. cancel; try reflexivity.
    + sep_apply_l_atomic R. cancel; try reflexivity.
  - simpl. unfold mu_matches; simpl. rewrite E; simpl.
    destruct (IH a v ND' F) as [L R]. unfold mu_matches in L, R. split.
    + sep_apply_l_atomic L. cancel; try reflexivity.
    + sep_apply_l_atomic R. cancel; try reflexivity.
  - simpl. unfold mu_matches; simpl. rewrite E; simpl.
    destruct (IH a v ND' F) as [L R]. unfold mu_matches in L, R. split.
    + sep_apply_l_atomic L. cancel; try reflexivity.
    + sep_apply_l_atomic R. cancel; try reflexivity.
  - simpl. unfold mu_matches; simpl. rewrite E; simpl.
    destruct (IH a v ND' F) as [L R]. unfold mu_matches in L, R. split.
    + sep_apply_l_atomic L. cancel; try reflexivity.
    + sep_apply_l_atomic R. cancel; try reflexivity.
  - simpl. unfold mu_matches; simpl. rewrite E; simpl.
    destruct (IH a v ND' F) as [L R]. unfold mu_matches in L, R. split.
    + sep_apply_l_atomic L. cancel; try reflexivity.
    + sep_apply_l_atomic R. cancel; try reflexivity.
Qed.
Lemma mu_word_lens__source_word_lenses : forall h a,
 mu_distinct h -> mu_readable h MUword a ->
 (naive_C_Rules.derivable1 (mu_heap h)
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a)) (mu_heap (mu_without h MUword a)))) /\
 (naive_C_Rules.derivable1
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a)) (mu_heap (mu_without h MUword a))) (mu_heap h)).
Proof.
 intros h a ND [v F]. unfold mu_value; rewrite F.
 apply mu_list_word_lens__source_word_lenses; assumption.
Qed.
Lemma mu_without_word_lookup__source_word_lenses : forall l a b,
 a <> b ->
 mu_find_cells (filter (fun c => negb (mu_matches MUword a c)) l) MUword b = mu_find_cells l MUword b.
Proof.
 induction l as [|[x k v] l IH]; intros a b N; simpl; auto.
 unfold mu_matches; simpl.
 destruct (Z.eqb x a) eqn:E; destruct k; simpl;
 destruct (Z.eqb x b) eqn:F; simpl; try apply IH; auto;
 apply Z.eqb_eq in E; apply Z.eqb_eq in F; congruence.
Qed.
Lemma mu_filter_distinct__source_word_lenses : forall l f,
 NoDup (map mu_address l) -> NoDup (map mu_address (filter f l)).
Proof.
 induction l as [|c l IH]; intros f ND; simpl; constructor || idtac.
 inversion ND as [|? ? N D]; subst.
 destruct (f c); simpl; [constructor|]; try (apply IH; exact D).
 intro H; apply N. apply in_map_iff in H as [x [E H]].
 apply filter_In in H as [H _]. apply in_map_iff; exists x; auto.
Qed.
Lemma mu_without_facts__source_word_lenses : forall h a b,
 a <> b -> mu_distinct h -> mu_readable h MUword b ->
 mu_distinct (mu_without h MUword a) /\
 mu_readable (mu_without h MUword a) MUword b /\
 mu_value (mu_without h MUword a) MUword b = mu_value h MUword b.
Proof.
 intros h a b N D R.
 assert (E: mu_find (mu_without h MUword a) MUword b = mu_find h MUword b).
 { apply mu_without_word_lookup__source_word_lenses; exact N. }
 split.
 - apply mu_filter_distinct__source_word_lenses; exact D.
 - split.
   + destruct R as [v F]. exists v. rewrite E. exact F.
   + unfold mu_value; rewrite E; reflexivity.
Qed.
Lemma mu_two_word_lens__source_word_lenses : forall h a b,
 mu_distinct h -> mu_readable h MUword a -> mu_readable h MUword b -> a <> b ->
 (naive_C_Rules.derivable1 (mu_heap h)
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a))
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint b (mu_value h MUword b))
     (mu_heap (mu_without (mu_without h MUword a) MUword b))))) /\
 (naive_C_Rules.derivable1
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a))
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint b (mu_value h MUword b))
     (mu_heap (mu_without (mu_without h MUword a) MUword b)))) (mu_heap h)).
Proof.
 Import naive_C_Rules.
 intros h a b D A B N.
 destruct (mu_word_lens__source_word_lenses h a D A) as [AL AR].
 destruct (mu_without_facts__source_word_lenses h a b N D B) as [D' [B' V]].
 destruct (mu_word_lens__source_word_lenses (mu_without h MUword a) b D' B') as [BL BR].
 rewrite V in BL, BR.
 split.
 - sep_apply_l_atomic AL. sep_apply_l_atomic BL. cancel; try reflexivity.
 - sep_apply_l_atomic BR. sep_apply_l_atomic AR. cancel; try reflexivity.
Qed.
Lemma mu_filter_absent__wrapper_guard_lenses : forall cs k a,
  ~ In a (map mu_address cs) ->
  filter (fun c => negb (mu_matches k a c)) cs = cs.
Proof.
  induction cs as [|c cs IH]; intros k a H; simpl; auto.
  assert (E : mu_matches k a c = false).
  { unfold mu_matches. assert (mu_address c <> a) by (intro E; apply H; simpl; auto).
    apply Z.eqb_neq in H0. rewrite H0. reflexivity. }
  rewrite E; simpl. f_equal. apply IH. intro J. apply H. simpl; auto.
Qed.
Lemma mu_cells_lens__wrapper_guard_lenses : forall cs k a v,
  NoDup (map mu_address cs) -> mu_find_cells cs k a = Some (Some v) ->
  naive_C_Rules.derivable1 (mu_cells_heap cs)
    (naive_C_Rules.sepcon (mu_cell_heap (MuCell a k (Some v)))
    (mu_cells_heap (filter (fun c => negb (mu_matches k a c)) cs))) /\
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mu_cell_heap (MuCell a k (Some v)))
    (mu_cells_heap (filter (fun c => negb (mu_matches k a c)) cs))) (mu_cells_heap cs).
Proof.
  Import naive_C_Rules.
  induction cs as [|[b j w] cs IH]; intros k a v Hnd Hfind; simpl in Hfind; try discriminate.
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct (Z.eqb b a && mu_kind_eqb j k)%bool eqn:E.
  - apply Bool.andb_true_iff in E. destruct E as [E K]. apply Z.eqb_eq in E; subst b.
    pose proof (mu_filter_absent__wrapper_guard_lenses cs k a Hnot) as F.
    unfold mu_matches in F.
    destruct j, k; simpl in K; try discriminate; inversion Hfind; subst w;
    simpl; unfold mu_matches; simpl; rewrite Z.eqb_refl; simpl;
    rewrite F;
    split; cancel.
  - specialize (IH k a v Htail Hfind). destruct IH as [IH1 IH2].
    change (mu_matches k a (MuCell b j w) = false) in E.
    cbn [filter]. rewrite E. cbn [negb]. cbn [mu_cells_heap].
    split.
    + sep_apply_l_atomic IH1. cancel.
    + sep_apply_r_atomic IH2. cancel.
  all: try reflexivity.
  all: try assumption.
Qed.
Lemma mu_guard_lens__wrapper_guard_lenses : forall h k a,
 mu_distinct h -> mu_readable h k a ->
 naive_C_Rules.derivable1 (mu_heap h)
 (naive_C_Rules.sepcon (mu_cell_heap (MuCell a k (Some (mu_value h k a)))) (mu_heap (mu_without h k a))) /\
 naive_C_Rules.derivable1
 (naive_C_Rules.sepcon (mu_cell_heap (MuCell a k (Some (mu_value h k a)))) (mu_heap (mu_without h k a))) (mu_heap h).
Proof.
 intros h k a H [v E]. unfold mu_value. rewrite E.
 unfold mu_heap, mu_without; simpl.
 apply mu_cells_lens__wrapper_guard_lenses; assumption.
Qed.
Lemma mu_distinct_without__wrapper_guard_lenses : forall h k a,
 mu_distinct h -> mu_distinct (mu_without h k a).
Proof.
 intros h k a. unfold mu_distinct, mu_without; simpl.
 induction (mu_cells h) as [|c cs IH]; simpl; intros H; auto.
 inversion H as [|? ? Hnot Htail]; subst.
 destruct (negb (mu_matches k a c)); simpl; auto.
 constructor; auto. intro J. apply in_map_iff in J.
 destruct J as [x [E J]]. apply filter_In in J. apply Hnot.
 apply in_map_iff. exists x; tauto.
Qed.
Lemma mu_cross_kind_filter__wrapper_guard_lenses : forall h a b,
 mu_find (mu_without h MUword a) MUbyte b = mu_find h MUbyte b.
Proof.
 intros h a b. unfold mu_find, mu_without; simpl.
 induction (mu_cells h) as [|[c k v] cs IH]; simpl; auto.
 unfold mu_matches in *. destruct k; simpl in *;
 destruct (Z.eqb c a) eqn:E; destruct (Z.eqb c b) eqn:F;
 simpl in *; rewrite ?E, ?F; simpl; auto.
Qed.
Lemma mu_guard_pair_lens__wrapper_guard_lenses : forall h a b,
 mu_distinct h -> mu_readable h MUword a -> mu_readable h MUbyte b ->
 naive_C_Rules.derivable1 (mu_heap h)
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a))
 (naive_C_Rules.sepcon (naive_C_Rules.store_uchar b (mu_value h MUbyte b))
 (mu_heap (mu_without (mu_without h MUword a) MUbyte b)))) /\
 naive_C_Rules.derivable1
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a))
 (naive_C_Rules.sepcon (naive_C_Rules.store_uchar b (mu_value h MUbyte b))
 (mu_heap (mu_without (mu_without h MUword a) MUbyte b)))) (mu_heap h).
Proof.
 Import naive_C_Rules.
 intros h a b Hnd Hw Hb.
 assert (Hb' : mu_readable (mu_without h MUword a) MUbyte b).
 { destruct Hb as [v E]. exists v. rewrite mu_cross_kind_filter__wrapper_guard_lenses. exact E. }
 assert (V : mu_value (mu_without h MUword a) MUbyte b = mu_value h MUbyte b).
 { unfold mu_value. rewrite mu_cross_kind_filter__wrapper_guard_lenses. reflexivity. }
 destruct (mu_guard_lens__wrapper_guard_lenses h MUword a Hnd Hw) as [W1 W2].
 destruct (mu_guard_lens__wrapper_guard_lenses (mu_without h MUword a) MUbyte b
   (mu_distinct_without__wrapper_guard_lenses h MUword a Hnd) Hb') as [B1 B2].
 rewrite V in B1, B2. cbn [mu_cell_heap mu_cell_kind mu_initial mu_address] in W1, W2, B1, B2.
 split.
 - sep_apply_l_atomic W1. sep_apply_l_atomic B1. cancel.
 - sep_apply_r_atomic W2. sep_apply_l_atomic B2. cancel.
Qed.
Lemma mu_absent_maps__simple_write_lenses : forall cs k a v,
  ~ In a (map mu_address cs) ->
  filter (fun c => negb (mu_matches k a c)) cs = cs /\
  map (fun c => if mu_matches k a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs = cs.
Proof.
  induction cs as [|c cs IH]; intros k a v H; simpl; [auto|].
  assert (E : mu_matches k a c = false).
  { unfold mu_matches. assert (mu_address c <> a) by (intro E; apply H; simpl; auto).
    apply Z.eqb_neq in H0. rewrite H0. reflexivity. }
  rewrite E. simpl. destruct (IH k a v) as [F M]; [intro I; apply H; simpl; auto|].
  rewrite F, M. auto.
Qed.
Lemma mu_set_distinct__simple_write_lenses : forall h k a v,
  mu_distinct h -> mu_distinct (mu_set h k a v).
Proof.
  intros [l cs] k a v H. unfold mu_distinct, mu_set in *. simpl in *.
  assert (E : map mu_address (map (fun c => if mu_matches k a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs) = map mu_address cs).
  { clear H. induction cs as [|c cs IH]; simpl; [reflexivity|].
    destruct (mu_matches k a c); simpl; rewrite IH; reflexivity. }
  rewrite E. exact H.
Qed.
Lemma mu_word_extract_cells__simple_write_lenses : forall cs a,
  NoDup (map mu_address cs) ->
  (exists v, mu_find_cells cs MUword a = Some v) ->
  (naive_C_Rules.derivable1 (mu_cells_heap cs) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs)))).
Proof.
  Import naive_C_Rules.
  induction cs as [|[b k o] cs IH]; intros a H [v F]; simpl in F; [discriminate|].
  inversion H as [|? ? N D]; subst.
  change ((if mu_matches MUword a (MuCell b k o) then Some o else mu_find_cells cs MUword a) = Some v) in F.
  destruct (mu_matches MUword a (MuCell b k o)) eqn:E.
  - assert (B : b = a /\ k = MUword).
    { unfold mu_matches in E; simpl in E. apply Bool.andb_true_iff in E.
      destruct E as [E K]. apply Z.eqb_eq in E. destruct k; simpl in K; try discriminate; split; auto. }
    destruct B; subst b k.
    destruct (mu_absent_maps__simple_write_lenses cs MUword a 0 N) as [Q _].
    change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mu_cell_heap (MuCell a MUword o)) (mu_cells_heap cs)) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) (MuCell a MUword o :: cs))))).
    simpl filter. rewrite E. simpl. rewrite Q. simpl mu_cell_heap.
    destruct o as [old|].
    + sep_apply_l_atomic (naive_C_Rules.store_uint_undef_store_uint a old). cancel.
    + unfold mu_cell_heap; simpl. cancel.
  - change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mu_cell_heap (MuCell b k o)) (mu_cells_heap cs)) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) (MuCell b k o :: cs))))).
    simpl filter. rewrite E. simpl negb. simpl filter. simpl mu_cells_heap.
    sep_apply_l_atomic (IH a D (ex_intro _ v F)). cancel.
Qed.
Lemma mu_word_write_extract__simple_write_lenses : forall h a,
  mu_distinct h -> mu_writable h MUword a ->
  (naive_C_Rules.derivable1 (mu_heap h) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mu_heap (mu_without h MUword a)))).
Proof.
  intros [l cs] a H W. apply mu_word_extract_cells__simple_write_lenses; assumption.
Qed.
Lemma mu_word_restore_cells__simple_write_lenses : forall cs a v,
  NoDup (map mu_address cs) ->
  (exists old, mu_find_cells cs MUword a = Some old) ->
  (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs))) (mu_cells_heap (map (fun c => if mu_matches MUword a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs))).
Proof.
  induction cs as [|[b k o] cs IH]; intros a v H [old F]; simpl in F; [discriminate|].
  inversion H as [|? ? N D]; subst.
  change ((if mu_matches MUword a (MuCell b k o) then Some o else mu_find_cells cs MUword a) = Some old) in F.
  destruct (mu_matches MUword a (MuCell b k o)) eqn:E.
  - assert (B : b = a /\ k = MUword).
    { unfold mu_matches in E; simpl in E. apply Bool.andb_true_iff in E.
      destruct E as [E K]. apply Z.eqb_eq in E. destruct k; simpl in K; try discriminate; split; auto. }
    destruct B; subst b k.
    destruct (mu_absent_maps__simple_write_lenses cs MUword a v N) as [Q M].
    simpl filter. simpl map. rewrite E. simpl negb. rewrite Q, M. simpl mu_cells_heap. unfold mu_cell_heap; simpl. cancel.
  - simpl filter. simpl map. rewrite E. simpl negb. simpl mu_cells_heap.
    sep_apply_r_atomic (IH a v D (ex_intro _ old F)). cancel. intros m Hm; exact Hm.
Qed.
Lemma mu_word_write_restore__simple_write_lenses : forall h a v,
  mu_distinct h -> mu_writable h MUword a ->
  (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mu_heap (mu_without h MUword a))) (mu_heap (mu_set h MUword a v))).
Proof.
  intros [l cs] a v H W. apply mu_word_restore_cells__simple_write_lenses; assumption.
Qed.
Lemma mu_copy_filter_absent__content_copy_lenses : forall cs k a,
 ~ In a (map mu_address cs) ->
 filter (fun c => negb (mu_matches k a c)) cs = cs.
Proof.
 intros cs k a; induction cs as [|c cs IH]; intros H; simpl; auto.
 assert (mu_matches k a c = false) as E.
 { unfold mu_matches. apply Bool.andb_false_iff. left. apply Z.eqb_neq. intro E; apply H; simpl; auto. }
 rewrite E; simpl. f_equal. apply IH. intro K; apply H; simpl; auto.
Qed.
Lemma mu_copy_set_absent__content_copy_lenses : forall cs k a v,
 ~ In a (map mu_address cs) ->
 map (fun c => if mu_matches k a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs = cs.
Proof.
 intros cs k a v; induction cs as [|c cs IH]; intros H; simpl; auto.
 assert (mu_matches k a c = false) as E.
 { unfold mu_matches. apply Bool.andb_false_iff. left. apply Z.eqb_neq. intro E; apply H; simpl; auto. }
 rewrite E. f_equal. apply IH. intro K; apply H; simpl; auto.
Qed.
Lemma mu_copy_set_distinct__content_copy_lenses : forall h k a v,
 mu_distinct h -> mu_distinct (mu_set h k a v).
Proof.
 intros [l cs] k a v H. unfold mu_distinct, mu_set in *; simpl in *.
 rewrite map_map. assert (map (fun c => mu_address (if mu_matches k a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c)) cs = map mu_address cs) as E.
 { apply map_ext. intro c. destruct (mu_matches k a c); reflexivity. }
 rewrite E; exact H.
Qed.
Lemma mu_copy_cells_lens__content_copy_lenses : forall cs a ov,
 NoDup (map mu_address cs) -> mu_find_cells cs MUword a = Some ov ->
 naive_C_Rules.derivable1 (mu_cells_heap cs) (naive_C_Rules.sepcon (mu_cell_heap (MuCell a MUword ov))
 (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs))).
Proof.
 Import naive_C_Rules.
 induction cs as [|[b k w] cs IH]; intros a ov ND F; simpl in F; try discriminate.
 inversion ND as [|? ? N D]; subst.
 unfold mu_matches; simpl.
 destruct ((b =? a) && mu_kind_eqb k MUword)%bool eqn:E.
 - apply Bool.andb_true_iff in E as [E K]. apply Z.eqb_eq in E; subst b.
   destruct k; simpl in K; try discriminate. inversion F; subst w.
   simpl. pose proof (mu_copy_filter_absent__content_copy_lenses cs MUword a N) as EF. unfold mu_matches in EF. rewrite EF.
   simpl. naive_C_Rules.sepcon_cancel.
 - simpl. specialize (IH a ov D F).
   unfold mu_matches in IH. naive_C_Rules.sep_apply_l_aux IH. naive_C_Rules.sepcon_cancel.
Qed.
Lemma mu_copy_cells_restore__content_copy_lenses : forall cs a ov v,
 NoDup (map mu_address cs) -> mu_find_cells cs MUword a = Some ov ->
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs)))
 (mu_cells_heap (map (fun c => if mu_matches MUword a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs)).
Proof.
 Import naive_C_Rules.
 induction cs as [|[b k w] cs IH]; intros a ov v ND F; simpl in F; try discriminate.
 inversion ND as [|? ? N D]; subst.
 unfold mu_matches; simpl.
 destruct ((b =? a) && mu_kind_eqb k MUword)%bool eqn:E.
 - apply Bool.andb_true_iff in E as [E K]. apply Z.eqb_eq in E; subst b.
   destruct k; simpl in K; try discriminate.
   simpl. pose proof (mu_copy_filter_absent__content_copy_lenses cs MUword a N) as EF. unfold mu_matches in EF. rewrite EF.
   pose proof (mu_copy_set_absent__content_copy_lenses cs MUword a v N) as ES. unfold mu_matches in ES. rewrite ES. simpl. naive_C_Rules.sepcon_cancel.
   cbn [mu_cell_heap mu_cell_kind mu_address mu_initial]. cancel.
 - simpl. specialize (IH a ov v D F).
   unfold mu_matches in IH. naive_C_Rules.sep_apply_l_aux IH. naive_C_Rules.sepcon_cancel.
Qed.
Lemma mu_copy_read_lens__content_copy_lenses : forall h a,
 mu_distinct h -> mu_readable h MUword a ->
 (mu_heap h |-- store_uint a (mu_value h MUword a) ** mu_heap (mu_without h MUword a))%sac.
Proof.
 intros [l cs] a D [v F]. unfold mu_value. rewrite F.
 unfold mu_heap, mu_without; simpl.
 exact (mu_copy_cells_lens__content_copy_lenses cs a (Some v) D F).
Qed.
Lemma mu_copy_write_lens__content_copy_lenses : forall h a,
 mu_distinct h -> mu_writable h MUword a ->
 (mu_heap h |-- undef_store_uint a ** mu_heap (mu_without h MUword a))%sac.
Proof.
 intros [l cs] a D [ov F]. unfold mu_heap, mu_without; simpl.
 sep_apply_l_atomic (mu_copy_cells_lens__content_copy_lenses cs a ov D F).
 destruct ov as [v|]; cbn [mu_cell_heap mu_cell_kind mu_address mu_initial].
 - sep_apply_l_atomic (store_uint_undef_store_uint a v). cancel.
 - cancel.
Qed.
Lemma mu_copy_restore_lens__content_copy_lenses : forall h a v,
 mu_distinct h -> mu_writable h MUword a ->
 (store_uint a v ** mu_heap (mu_without h MUword a) |-- mu_heap (mu_set h MUword a v))%sac.
Proof.
 intros [l cs] a v D [ov F]. unfold mu_heap, mu_without, mu_set; simpl.
 exact (mu_copy_cells_restore__content_copy_lenses cs a ov v D F).
Qed.
Lemma mu_copy_without_distinct__content_copy_lenses : forall h k a,
 mu_distinct h -> mu_distinct (mu_without h k a).
Proof.
 intros [l cs] k a D. unfold mu_distinct, mu_without in *; simpl in *.
 induction cs as [|c cs IH]; simpl in *; auto.
 inversion D as [|? ? N DD]; subst.
 destruct (negb (mu_matches k a c)); simpl; auto.
 constructor; auto. intro H. apply in_map_iff in H as [x [E I]].
 apply filter_In in I as [I _]. apply N. apply in_map_iff. exists x; auto.
Qed.
Lemma mu_copy_match_addr__content_copy_lenses : forall c k a,
 mu_matches k a c = true -> mu_address c = a.
Proof. intros c k a E. unfold mu_matches in E. apply Bool.andb_true_iff in E as [E _]. now apply Z.eqb_eq in E. Qed.
Lemma mu_copy_find_without__content_copy_lenses : forall cs a b,
 a <> b ->
 mu_find_cells (filter (fun c => negb (mu_matches MUword a c)) cs) MUword b = mu_find_cells cs MUword b.
Proof.
 induction cs as [|c cs IH]; intros a b N; simpl; auto.
 fold (mu_matches MUword b c).
 destruct (mu_matches MUword a c) eqn:A; simpl.
 - assert (mu_matches MUword b c = false) as B.
   { destruct (mu_matches MUword b c) eqn:B; auto. exfalso. apply N.
     pose proof (mu_copy_match_addr__content_copy_lenses c MUword a A).
     pose proof (mu_copy_match_addr__content_copy_lenses c MUword b B). congruence. }
   rewrite B. apply IH; auto.
 - simpl. fold (mu_matches MUword b c). destruct (mu_matches MUword b c); auto.
Qed.
Lemma mu_copy_writable_without__content_copy_lenses : forall h a b,
 a <> b -> mu_writable h MUword b -> mu_writable (mu_without h MUword a) MUword b.
Proof.
 intros [l cs] a b N [v F]. exists v. unfold mu_find, mu_without; simpl.
 rewrite mu_copy_find_without__content_copy_lenses by auto. exact F.
Qed.
Lemma mu_copy_cells_readback__content_copy_lenses : forall cs a ov,
 NoDup (map mu_address cs) -> mu_find_cells cs MUword a = Some ov ->
 (mu_cell_heap (MuCell a MUword ov) ** mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs) |-- mu_cells_heap cs)%sac.
Proof.
 induction cs as [|[b k w] cs IH]; intros a ov ND F; simpl in F; try discriminate.
 inversion ND as [|? ? N D]; subst.
 unfold mu_matches; simpl.
 destruct ((b =? a) && mu_kind_eqb k MUword)%bool eqn:E.
 - apply Bool.andb_true_iff in E as [E K]. apply Z.eqb_eq in E; subst b.
   destruct k; simpl in K; try discriminate. inversion F; subst w.
   simpl. pose proof (mu_copy_filter_absent__content_copy_lenses cs MUword a N) as EF.
   unfold mu_matches in EF. rewrite EF. simpl. cancel.
 - simpl. specialize (IH a ov D F). unfold mu_matches in IH.
   sep_apply_l_atomic IH. cancel.
Qed.
Lemma mu_copy_readback__content_copy_lenses : forall h a,
 mu_distinct h -> mu_readable h MUword a ->
 (store_uint a (mu_value h MUword a) ** mu_heap (mu_without h MUword a) |-- mu_heap h)%sac.
Proof.
 intros [l cs] a D [v F]. unfold mu_value. rewrite F.
 unfold mu_heap, mu_without; simpl.
 exact (mu_copy_cells_readback__content_copy_lenses cs a (Some v) D F).
Qed.
Lemma mu_copy_find_set_other__content_copy_lenses : forall cs a b v,
 a <> b ->
 mu_find_cells (map (fun c => if mu_matches MUword a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs) MUword b = mu_find_cells cs MUword b.
Proof.
 induction cs as [|[c k ov] cs IH]; intros a b v N; simpl; auto.
 unfold mu_matches in *; simpl. destruct k; simpl;
 destruct (c =? a) eqn:A; destruct (c =? b) eqn:B; simpl; try rewrite B; simpl; auto;
 try (rewrite IH by auto; reflexivity).
 all: try (apply Z.eqb_eq in A; apply Z.eqb_eq in B; congruence).
Qed.
Lemma mu_copy_filter_updates__content_copy_lenses : forall h a b v,
 a <> b ->
 mu_without (mu_set h MUword b v) MUword a = mu_set (mu_without h MUword a) MUword b v.
Proof.
 intros [l cs] a b v N. unfold mu_without, mu_set; simpl. f_equal.
 induction cs as [|[c k ov] cs IH]; simpl; auto.
 unfold mu_matches in *; simpl in *. destruct k; simpl in *;
 destruct (c =? a) eqn:A; destruct (c =? b) eqn:B; simpl;
 try rewrite A; try rewrite B; simpl; try rewrite IH; try reflexivity.
Qed.
Lemma mu_copy_distinct_extract__content_copy_lenses : forall h a b,
 mu_distinct h -> mu_readable h MUword a -> mu_writable h MUword b -> a <> b ->
 (mu_heap h |-- store_uint a (mu_value h MUword a) ** undef_store_uint b **
 mu_heap (mu_without (mu_without h MUword a) MUword b))%sac.
Proof.
 intros h a b D R W N.
 sep_apply_l_atomic (mu_copy_read_lens__content_copy_lenses h a D R).
 pose proof (mu_copy_without_distinct__content_copy_lenses h MUword a D) as DD.
 pose proof (mu_copy_writable_without__content_copy_lenses h a b N W) as WW.
 sep_apply_l_atomic (mu_copy_write_lens__content_copy_lenses (mu_without h MUword a) b DD WW).
 cancel.
Qed.
Lemma mu_copy_distinct_restore__content_copy_lenses : forall h a b v,
 mu_distinct h -> mu_readable h MUword a -> mu_writable h MUword b -> a <> b ->
 (store_uint a (mu_value h MUword a) ** store_uint b v **
 mu_heap (mu_without (mu_without h MUword a) MUword b) |-- mu_heap (mu_set h MUword b v))%sac.
Proof.
 intros h a b v D R W N.
 pose proof (mu_copy_without_distinct__content_copy_lenses h MUword a D) as DD.
 pose proof (mu_copy_writable_without__content_copy_lenses h a b N W) as WW.
 sep_apply_l_atomic (mu_copy_restore_lens__content_copy_lenses (mu_without h MUword a) b v DD WW).
 rewrite <- (mu_copy_filter_updates__content_copy_lenses h a b v N).
 assert (mu_find (mu_set h MUword b v) MUword a = mu_find h MUword a) as F.
 { unfold mu_find, mu_set; simpl. apply mu_copy_find_set_other__content_copy_lenses. congruence. }
 assert (mu_readable (mu_set h MUword b v) MUword a) as RR.
 { destruct R as [x R]. exists x. rewrite F. exact R. }
 pose proof (mu_copy_set_distinct__content_copy_lenses h MUword b v D) as DDD.
 pose proof (mu_copy_readback__content_copy_lenses (mu_set h MUword b v) a DDD RR) as BACK.
 unfold mu_value in BACK. rewrite F in BACK. fold (mu_value h MUword a) in BACK. sep_apply_l_atomic BACK. cancel.
Qed.
Lemma mu_absent_filter__right_clear_lenses : forall cs a,
  ~ In a (map mu_address cs) ->
  filter (fun c => negb (mu_matches MUword a c)) cs = cs.
Proof.
  induction cs as [|c cs IH]; intros a H; simpl; auto.
  assert (Hne : mu_address c <> a) by (intro E; apply H; left; exact E).
  assert (Ht : ~ In a (map mu_address cs)) by (intro E; apply H; right; exact E).
  unfold mu_matches at 1. rewrite (proj2 (Z.eqb_neq _ _) Hne). simpl.
  rewrite IH by exact Ht. reflexivity.
Qed.
Lemma mu_absent_set__right_clear_lenses : forall cs a v,
  ~ In a (map mu_address cs) ->
  map (fun c => if mu_matches MUword a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs = cs.
Proof.
  induction cs as [|c cs IH]; intros a v H; simpl; auto.
  assert (Hne : mu_address c <> a) by (intro E; apply H; left; exact E).
  assert (Ht : ~ In a (map mu_address cs)) by (intro E; apply H; right; exact E).
  unfold mu_matches at 1. rewrite (proj2 (Z.eqb_neq _ _) Hne). simpl.
  rewrite IH by exact Ht. reflexivity.
Qed.
Lemma mu_clear_read_cells__right_clear_lenses : forall cs a v,
  NoDup (map mu_address cs) -> mu_find_cells cs MUword a = Some (Some v) ->
  naive_C_Rules.derivable1 (mu_cells_heap cs)
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v)
      (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs))).
Proof.
  Import naive_C_Rules.
  induction cs as [|[b k o] cs IH]; intros a v Hnd Hfind; simpl in Hfind; try discriminate.
  inversion Hnd as [|? ? Hnot Htail]; subst.
  change ((if mu_matches MUword a (MuCell b k o) then Some o else mu_find_cells cs MUword a) = Some (Some v)) in Hfind.
  destruct (mu_matches MUword a (MuCell b k o)) eqn:E.
  - cbn [mu_cells_heap filter map]. rewrite E. cbn [negb].
    unfold mu_matches in E; simpl in E. apply Bool.andb_true_iff in E. destruct E as [Eb Ek].
    apply Z.eqb_eq in Eb; subst b. destruct k; simpl in Ek; try discriminate.
    inversion Hfind; subst o. cbn [mu_cell_heap mu_cell_kind mu_initial mu_address].
    rewrite mu_absent_filter__right_clear_lenses by exact Hnot.
    naive_C_Rules.cancel_exactly1_or_fail (naive_C_Rules.store_uint a v).
    naive_C_Rules.sepcon_cancel.
  - cbn [mu_cells_heap filter]. rewrite E. simpl.
    naive_C_Rules.sep_apply_left (IH a v Htail Hfind).
    naive_C_Rules.cancel_exactly1_or_fail (mu_cell_heap (MuCell b k o)).
    naive_C_Rules.sepcon_cancel.
Qed.
Lemma mu_clear_read_lens__right_clear_lenses : forall h a,
  mu_distinct h -> mu_readable h MUword a ->
  naive_C_Rules.derivable1 (mu_heap h)
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mu_value h MUword a))
       (mu_heap (mu_without h MUword a))).
Proof.
  intros h a Hd [v Hv]. unfold mu_value. rewrite Hv.
  unfold mu_heap, mu_without; simpl. apply mu_clear_read_cells__right_clear_lenses; assumption.
Qed.
Lemma mu_clear_write_cells__right_clear_lenses : forall cs a old v,
  NoDup (map mu_address cs) -> mu_find_cells cs MUword a = Some old ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v)
      (mu_cells_heap (filter (fun c => negb (mu_matches MUword a c)) cs)))
    (mu_cells_heap (map (fun c => if mu_matches MUword a c then MuCell (mu_address c) (mu_cell_kind c) (Some v) else c) cs)).
Proof.
  Import naive_C_Rules.
  induction cs as [|[b k o] cs IH]; intros a old v Hnd Hfind; simpl in Hfind; try discriminate.
  inversion Hnd as [|? ? Hnot Htail]; subst.
  change ((if mu_matches MUword a (MuCell b k o) then Some o else mu_find_cells cs MUword a) = Some old) in Hfind.
  destruct (mu_matches MUword a (MuCell b k o)) eqn:E.
  - cbn [mu_cells_heap filter map]. rewrite E. cbn [negb].
    unfold mu_matches in E; simpl in E. apply Bool.andb_true_iff in E. destruct E as [Eb Ek].
    apply Z.eqb_eq in Eb; subst b. destruct k; simpl in Ek; try discriminate.
    cbn [mu_cell_heap mu_cells_heap mu_cell_kind mu_initial mu_address].
    rewrite mu_absent_filter__right_clear_lenses by exact Hnot.
    rewrite mu_absent_set__right_clear_lenses by exact Hnot.
    naive_C_Rules.cancel_exactly1_or_fail (naive_C_Rules.store_uint a v).
    naive_C_Rules.sepcon_cancel.
  - cbn [mu_cells_heap filter map]. rewrite E. simpl.
    naive_C_Rules.sep_apply_right (IH a old v Htail Hfind).
    naive_C_Rules.cancel_exactly1_or_fail (mu_cell_heap (MuCell b k o)).
    naive_C_Rules.sepcon_cancel.
Qed.
Lemma mu_clear_write_restore__right_clear_lenses : forall h a v,
  mu_distinct h -> mu_writable h MUword a ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mu_heap (mu_without h MUword a)))
    (mu_heap (mu_set h MUword a v)).
Proof.
  intros h a v Hd [old Hfind]. unfold mu_heap, mu_without, mu_set; simpl.
  eapply mu_clear_write_cells__right_clear_lenses; eauto.
Qed.
Lemma mu_clear_distinct__right_clear_lenses : forall h k a v,
  mu_distinct h -> mu_distinct (mu_set h k a v).
Proof.
  intros h k a v H. unfold mu_distinct, mu_set in *; simpl.
  rewrite map_map. replace (map (fun x => mu_address (if mu_matches k a x then MuCell (mu_address x) (mu_cell_kind x) (Some v) else x)) (mu_cells h)) with (map mu_address (mu_cells h)).
  - exact H.
  - apply map_ext. intros c. destruct (mu_matches k a c); reflexivity.
Qed.
Lemma mu_remove_ptr_byte__wrapper_entry_safety h a b :
 mu_find (mu_without h MUptr a) MUbyte b = mu_find h MUbyte b.
Proof.
 unfold mu_find, mu_without, mu_matches; simpl.
 induction (mu_cells h) as [|[x k v] tl IH]; simpl; auto.
 destruct k; simpl; rewrite ?Bool.andb_false_r, ?Bool.andb_true_r; simpl;
 try (destruct (x =? a); simpl); rewrite ?Bool.andb_false_r, ?Bool.andb_true_r; simpl; auto.
 all: try (destruct (x =? b); auto).
Qed.
Lemma mu_filter_distinct__wrapper_entry_safety h k a :
 mu_distinct h -> mu_distinct (mu_without h k a).
Proof.
 unfold mu_distinct, mu_without; simpl.
 induction (mu_cells h) as [|c tl IH]; simpl; intros H; auto.
 inversion H as [|? ? Hnot Hdup]; subst.
 destruct (negb (mu_matches k a c)); simpl; auto.
 constructor; auto. intro Hin. apply Hnot.
 apply in_map_iff in Hin. destruct Hin as [x [Hx Hin]].
 apply filter_In in Hin. apply in_map_iff. exists x. tauto.
Qed.
Lemma mu_find_member__wrapper_call_safety cs k a v :
 mu_find_cells cs k a = Some v ->
 exists c, In c cs /\ mu_address c = a /\ mu_cell_kind c = k.
Proof.
 induction cs as [|c cs IH]; simpl; intros H; [discriminate|].
 destruct (Z.eqb (mu_address c) a && mu_kind_eqb (mu_cell_kind c) k)%bool eqn:E.
 - apply Bool.andb_true_iff in E. destruct E as [Ea Ek].
   apply Z.eqb_eq in Ea. exists c. split; [left; reflexivity|]. split; auto.
   destruct (mu_cell_kind c), k; simpl in Ek; congruence.
 - destruct (IH H) as [x [Hx Hrest]]. exists x. split; [right; exact Hx|exact Hrest].
Qed.
Lemma mu_cell_address_unique__wrapper_call_safety cs c d :
 NoDup (map mu_address cs) -> In c cs -> In d cs ->
 mu_address c = mu_address d -> c = d.
Proof.
 induction cs as [|x cs IH]; simpl; intros H Hc Hd E; [contradiction|].
 inversion H as [|? ? Hnot Hnd]; subst.
 destruct Hc as [Hc|Hc], Hd as [Hd|Hd].
 - congruence.
 - subst c. exfalso. apply Hnot. rewrite E. apply in_map. exact Hd.
 - subst d. exfalso. apply Hnot. rewrite <- E. apply in_map. exact Hc.
 - eapply IH; eauto.
Qed.
Lemma mu_readable_kind_address_distinct__wrapper_call_safety h k a k2 b :
 mu_distinct h -> mu_readable h k a -> mu_readable h k2 b ->
 k <> k2 -> a <> b.
Proof.
 unfold mu_distinct, mu_readable, mu_find.
 intros H [v Hv] [w Hw] Hk E.
 destruct (mu_find_member__wrapper_call_safety _ _ _ _ Hv) as [c [Hc [Hca Hck]]].
 destruct (mu_find_member__wrapper_call_safety _ _ _ _ Hw) as [d [Hd [Hda Hdk]]].
 assert (c = d) by (eapply mu_cell_address_unique__wrapper_call_safety; eauto; congruence).
 congruence.
Qed.
Lemma mu_entail_reassociate__wrapper_call_safety
 (a b c d e f g h q : naive_C_Rules.expr) :
 naive_C_Rules.derivable1
 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon a b) c) d) e) f) g) h) q ->
 naive_C_Rules.derivable1
 (naive_C_Rules.sepcon a (naive_C_Rules.sepcon b (naive_C_Rules.sepcon c (naive_C_Rules.sepcon d (naive_C_Rules.sepcon e (naive_C_Rules.sepcon f (naive_C_Rules.sepcon g h))))))) q.
Proof.
 Import naive_C_Rules.
 intros H. sep_apply_r_atomic H. Rename sepcon_assoc_change. cancel.
Qed.
