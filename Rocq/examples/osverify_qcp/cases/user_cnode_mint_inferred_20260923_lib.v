(* Independently inferred from the two bounded mint implementations.
   No old kernel specification/model/proof or verified program example used.
   Sequential ordinary-memory projection: critical markers are identities. *)
From Coq Require Import ZArith List String Bool.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* Finite typed physical cells. The list owns each actual cell once, regardless
   of how many priorities or capability pointers name it. None is write-only.
   These definitions compose existing primitive stores; they introduce no new
   memory semantics. kind 0 = uint32, 1 = uchar, 2 = pointer. *)
Record MintCell := mint_cell {
  mint_kind : Z;
  mint_address : Z;
  mint_initial : option Z
}.
Definition MintState := list MintCell.
Definition mint_cell_heap (c : MintCell) : naive_C_Rules.expr :=
  match mint_kind c, mint_initial c with
  | 0, Some v => naive_C_Rules.store_uint (mint_address c) v
  | 0, None => naive_C_Rules.undef_store_uint (mint_address c)
  | 1, Some v => naive_C_Rules.store_uchar (mint_address c) v
  | 1, None => naive_C_Rules.undef_store_uchar (mint_address c)
  | 2, Some v => naive_C_Rules.store_ptr (mint_address c) v
  | 2, None => naive_C_Rules.undef_store_ptr (mint_address c)
  | _, _ => naive_C_Rules.coq_prop False
  end.
Definition mint_heap (h : MintState) : naive_C_Rules.expr :=
  fold_right (fun c tail => naive_C_Rules.sepcon (mint_cell_heap c) tail)
             naive_C_Rules.emp h.
Definition mint_wellformed (h : MintState) : Prop :=
  NoDup (map mint_address h) /\
  Forall (fun c => 0 <= mint_kind c <= 2) h.
Definition mint_find (h : MintState) (a : Z) : option MintCell :=
  find (fun c => Z.eqb (mint_address c) a) h.
Definition mint_value (h : MintState) (a : Z) : Z :=
  match mint_find h a with
  | Some c => match mint_initial c with Some v => v | None => 0 end
  | None => 0
  end.
Definition mint_readable (h : MintState) (k a : Z) : Prop :=
  exists v, mint_find h a = Some (mint_cell k a (Some v)).
Definition mint_writable (h : MintState) (k a : Z) : Prop :=
  exists v, mint_find h a = Some (mint_cell k a v).
Definition mint_source_reads (h : MintState) (ty ri : Z) : Prop :=
  mint_readable h 0 ty /\ (mint_value h ty = 1 -> mint_readable h 0 ri).
Definition mint_auth_reads (h : MintState) (ar pa : Z) : Prop :=
  mint_readable h 0 ar /\ (Z.land (mint_value h ar) 1 <> 0 -> mint_readable h 1 pa).
Definition mint_u32 (v : Z) : Prop := 0 <= v <= 4294967295.
Definition mint_u8 (v : Z) : Prop := 0 <= v <= 255.

(* Explicit physical addresses bound by the C contract, not an axiom relating
   the legacy eval_addr_expr interface to frontend-generated addresses. *)
Record MintLayout := mint_layout {
  mint_dt : Z; mint_st : Z;
  mint_dty : Z; mint_dco : Z; mint_dri : Z;
  mint_sty : Z; mint_sco : Z; mint_sri : Z;
  mint_cp : Z; mint_pr : Z; mint_ct : Z; mint_ar : Z; mint_pa : Z
}.
Definition mint_core_layout (L : MintLayout) (dt st dty dco dri sty sco sri : Z) : Prop :=
  mint_dt L = dt /\ mint_st L = st /\
  mint_dty L = dty /\ mint_dco L = dco /\ mint_dri L = dri /\
  mint_sty L = sty /\ mint_sco L = sco /\ mint_sri L = sri.
Definition mint_user_layout (L : MintLayout) (cp pr ct ar pa : Z) : Prop :=
  mint_cp L = cp /\ mint_pr L = pr /\ mint_ct L = ct /\
  mint_ar L = ar /\ mint_pa L = pa.
Definition mint_dst (h : MintState) (L : MintLayout) : Z := mint_value h (mint_dt L).
Definition mint_src (h : MintState) (L : MintLayout) : Z := mint_value h (mint_st L).
Definition mint_cur (h : MintState) (L : MintLayout) : Z := mint_value h (mint_ct L).
Definition mint_remove (h : MintState) (a : Z) : MintState :=
  filter (fun c => negb (Z.eqb (mint_address c) a)) h.
Definition mint_set (h : MintState) (a v : Z) : MintState :=
  map (fun c => if Z.eqb (mint_address c) a
       then mint_cell (mint_kind c) (mint_address c) (Some v) else c) h.

(* Strict bit-set inclusion, with exactly a 32-bit unsigned complement. *)
Definition mint_proper_rights (old requested : Z) : Prop :=
  Z.land (Z.lxor old 4294967295) requested = 0 /\ old <> requested.
Definition mint_parameters_valid (d s f : Z) : Prop :=
  0 <= d < 64 /\ 0 <= s < 64 /\ 0 <= f <= 16.
Definition mint_eligible (h : MintState) (L : MintLayout) (d s f r : Z) : Prop :=
  mint_parameters_valid d s f /\
  mint_dst h L <> 0 /\ mint_src h L <> 0 /\
  mint_value h (mint_sty L) = 1 /\
  mint_proper_rights (mint_value h (mint_sri L)) r.

(* Necessary read/write resources only. Guards encode short-circuit access:
   destination storage is not required until a successful assignment is due.
   Source content is read after the type store, which may initialize its cell. *)
Definition mint_core_access (h : MintState) (L : MintLayout) (d s f r : Z) : Prop :=
  mint_parameters_valid d s f ->
  mint_readable h 2 (mint_dt L) /\
  mint_readable h 2 (mint_st L) /\
  (mint_dst h L <> 0 /\ mint_src h L <> 0 ->
    mint_readable h 0 (mint_sty L) /\
    (mint_value h (mint_sty L) = 1 ->
      mint_readable h 0 (mint_sri L)) /\
    (mint_eligible h L d s f r ->
      mint_readable (mint_set h (mint_dty L) 1) 0 (mint_sco L) /\
      mint_writable h 0 (mint_dty L) /\
      mint_writable h 0 (mint_dco L) /\
      mint_writable h 0 (mint_dri L))).
Definition mint_core_pre (h : MintState) (L : MintLayout) (d s f r : Z) : Prop :=
  mint_wellformed h /\ mint_u8 d /\ mint_u8 s /\ mint_u32 f /\
  mint_u32 r /\ mint_core_access h L d s f r.

(* A closed field-update relation. The category content is sampled after the
   type assignment: even a coinciding physical source-content/type cell is
   accounted for. With ordinary whole-object aliases that equality is false.
   The right field has last-write priority. All other cells retain their old
   address, type and optional value, including union pointer storage. *)
Definition mint_updated_cell (h : MintState) (L : MintLayout) (d s f r : Z)
                            (c : MintCell) : MintCell :=
  let dt := mint_dty L in
  let dc := mint_dco L in
  let dr := mint_dri L in
  let sc := mint_sco L in
  let copied := if Z.eqb sc dt then 1 else mint_value h sc in
  if Z.eqb (mint_address c) dr then mint_cell (mint_kind c) (mint_address c) (Some r)
  else if Z.eqb (mint_address c) dc then mint_cell (mint_kind c) (mint_address c) (Some copied)
  else if Z.eqb (mint_address c) dt then mint_cell (mint_kind c) (mint_address c) (Some 1)
  else c.
Definition mint_updated (h : MintState) (L : MintLayout) (d s f r : Z) : MintState :=
  map (mint_updated_cell h L d s f r) h.
Definition mint_core_result (h : MintState) (L : MintLayout) (d s f r ret : Z)
                            (after : MintState) : Prop :=
  (mint_eligible h L d s f r /\ ret = 0 /\ after = mint_updated h L d s f r) \/
  (~ mint_eligible h L d s f r /\ ret = 5 /\ after = h).

Definition mint_user_parameters_valid (d s : Z) : Prop :=
  0 <= d < 63 /\ 0 <= s < 63.
Definition mint_authorized (h : MintState) (L : MintLayout) (d s : Z) : Prop :=
  Z.land (mint_value h (mint_ar L)) 1 <> 0 /\
  mint_value h (mint_pa L) = s.
Definition mint_user_access (h : MintState) (L : MintLayout) (d s f r : Z) : Prop :=
  mint_user_parameters_valid d s ->
  mint_readable h 2 (mint_cp L) /\
  mint_value h (mint_cp L) <> 0 /\
  mint_readable h 1 (mint_pr L) /\
  0 <= mint_value h (mint_pr L) < 64 /\
  mint_readable h 2 (mint_ct L) /\
  (mint_cur h L <> 0 ->
    mint_readable h 0 (mint_ar L) /\
    (Z.land (mint_value h (mint_ar L)) 1 <> 0 ->
      mint_readable h 1 (mint_pa L)) /\
    (mint_authorized h L d s -> mint_core_access h L d s f r)).
Definition mint_user_pre (h : MintState) (L : MintLayout) (d s f r : Z) : Prop :=
  mint_wellformed h /\ mint_u8 d /\ mint_u8 s /\ mint_u32 f /\
  mint_u32 r /\ mint_user_access h L d s f r.
Definition mint_user_result (h : MintState) (L : MintLayout) (d s f r ret : Z)
                            (after : MintState) : Prop :=
  (~ mint_user_parameters_valid d s /\ ret = 42 /\ after = h) \/
  (mint_user_parameters_valid d s /\ mint_cur h L = 0 /\
     ret = 5 /\ after = h) \/
  (mint_user_parameters_valid d s /\ mint_cur h L <> 0 /\
     ~ mint_authorized h L d s /\ ret = 252 /\ after = h) \/
  (mint_user_parameters_valid d s /\ mint_cur h L <> 0 /\
     mint_authorized h L d s /\ mint_core_result h L d s f r ret after).

From Coq Require Import Lia.
Lemma mint_sep_assoc__core_access (P Q R : naive_C_Rules.expr) :
  naive_C_Rules.logic_equiv
    (naive_C_Rules.sepcon (naive_C_Rules.sepcon P Q) R)
    (naive_C_Rules.sepcon P (naive_C_Rules.sepcon Q R)).
Proof.
  unfold naive_C_Rules.logic_equiv, naive_C_Rules.derivable1, naive_C_Rules.sepcon.
  split.
  - intros m [mpq [mr [Hj [[mp [mq [Hpq [HP HQ]]]] HR]]]].
    destruct (naive_C_Rules.join_assoc mp mq mr mpq m Hpq Hj)
      as [mqr [Hqr Htotal]].
    exists mp, mqr. split; [exact Htotal|]. split; [exact HP|].
    exists mq, mr. auto.
  - intros m [mp [mqr [Hj [HP [mq [mr [Hqr [HQ HR]]]]]]]].
    pose proof (naive_C_Rules.join_comm _ _ _ Hj) as Hj'.
    pose proof (naive_C_Rules.join_comm _ _ _ Hqr) as Hqr'.
    destruct (naive_C_Rules.join_assoc mr mq mp mqr m Hqr' Hj')
      as [mqp [Hqp Htotal]].
    exists mqp, mr. split; [apply naive_C_Rules.join_comm; exact Htotal|].
    split; [|exact HR]. exists mp, mq.
    split; [apply naive_C_Rules.join_comm; exact Hqp|]. auto.
Qed.
Lemma mint_assoc9__core_access (P1 P2 P3 P4 P5 P6 P7 P8 P9 Q : naive_C_Rules.expr) :
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) Q ->
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 P9)))))))) Q.
Proof.
  intros H.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hd.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Hr.
  repeat rewrite mint_sep_assoc__core_access in H.
  exact H.
Qed.
Lemma mint_assoc10__core_access (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 Q : naive_C_Rules.expr) :
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) P10) Q ->
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 (naive_C_Rules.sepcon P9 P10))))))))) Q.
Proof.
  intros H.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hd.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Hr.
  repeat rewrite mint_sep_assoc__core_access in H.
  exact H.
Qed.
Lemma set_addresses__core_update_access : forall h a v,
  map mint_address (mint_set h a v) = map mint_address h.
Proof.
  intros h a v. induction h as [|c t IH]; simpl; auto.
  unfold mint_set in *. simpl in *. destruct (Z.eqb (mint_address c) a); simpl; now rewrite IH.
Qed.
Lemma set_wellformed__core_update_access : forall h a v,
  mint_wellformed h -> mint_wellformed (mint_set h a v).
Proof.
  intros h a v [HN HF]. split.
  - rewrite set_addresses__core_update_access. exact HN.
  - clear HN. unfold mint_set. induction HF; simpl; constructor; auto.
    destruct (Z.eqb (mint_address x) a); simpl; exact H.
Qed.
Lemma set_writable__core_update_access : forall h a v k b,
  mint_writable h k b -> mint_writable (mint_set h a v) k b.
Proof.
  intros h a v k b. unfold mint_writable, mint_find, mint_set.
  induction h as [|c t IH]; simpl; intros [w HW]; try discriminate.
  destruct (Z.eqb (mint_address c) b) eqn:EB.
  - inversion HW; subst c. simpl.
    destruct (Z.eqb b a); simpl; rewrite Z.eqb_refl; eexists; reflexivity.
  - destruct (Z.eqb (mint_address c) a) eqn:EA; simpl; rewrite EB;
      apply IH; exists w; exact HW.
Qed.
Lemma set_preserves__core_update_access : forall h a v,
  (mint_wellformed h -> mint_wellformed (mint_set h a v)) /\
  (forall k b, mint_writable h k b -> mint_writable (mint_set h a v) k b).
Proof.
  intros. split; intros; [apply set_wellformed__core_update_access | apply set_writable__core_update_access]; assumption.
Qed.
Lemma success_access__core_update_access : forall h L d s f r,
  mint_core_pre h L d s f r -> mint_eligible h L d s f r ->
  mint_wellformed h /\
  mint_readable (mint_set h (mint_dty L) 1) 0 (mint_sco L) /\
  mint_writable h 0 (mint_dty L) /\
  mint_writable h 0 (mint_dco L) /\
  mint_writable h 0 (mint_dri L).
Proof.
  intros h L d s f r [WF [_ [_ [_ [_ AC]]]]] EL.
  destruct EL as [PV [DN [SN REST]]].
  unfold mint_core_access in AC.
  destruct (AC PV) as [_ [_ AC2]].
  destruct (AC2 (conj DN SN)) as [_ [_ AC3]].
  specialize (AC3 (conj PV (conj DN (conj SN REST)))).
  tauto.
Qed.
Lemma associate9__core_update_access : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 Q : naive_C_Rules.expr,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 P9)))))))) Q.
Proof.
  intros. revert H.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hder.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Href.
  pose proof naive_C_Rules.logic_equiv_symm_instance as Hsym.
  pose proof naive_C_Rules.logic_equiv_trans_instance as Htrans.
  naive_C_Rules.sepcon_assoc_change. auto.
Qed.
Lemma associate10__core_update_access : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 Q : naive_C_Rules.expr,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) P10) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 (naive_C_Rules.sepcon P9 P10))))))))) Q.
Proof.
  intros. revert H.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hder.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Href.
  pose proof naive_C_Rules.logic_equiv_symm_instance as Hsym.
  pose proof naive_C_Rules.logic_equiv_trans_instance as Htrans.
  naive_C_Rules.sepcon_assoc_change. auto.
Qed.
Lemma mint_assoc8__user_pointer_access : forall P1 P2 P3 P4 P5 P6 P7 P8 Q : naive_C_Rules.expr,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 P8))))))) Q.
Proof.
  intros P1 P2 P3 P4 P5 P6 P7 P8 Q.
  Import naive_C_Rules.
  sepcon_assoc_change.
  tauto.
Qed.
Lemma mint_assoc9__user_pointer_access : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 Q : naive_C_Rules.expr,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 P9)))))))) Q.
Proof.
  intros P1 P2 P3 P4 P5 P6 P7 P8 P9 Q.
  Import naive_C_Rules.
  sepcon_assoc_change.
  tauto.
Qed.
Lemma mint_assoc10__user_pointer_access : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 Q : naive_C_Rules.expr,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon P1 P2) P3) P4) P5) P6) P7) P8) P9) P10) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P1 (naive_C_Rules.sepcon P2 (naive_C_Rules.sepcon P3 (naive_C_Rules.sepcon P4 (naive_C_Rules.sepcon P5 (naive_C_Rules.sepcon P6 (naive_C_Rules.sepcon P7 (naive_C_Rules.sepcon P8 (naive_C_Rules.sepcon P9 P10))))))))) Q.
Proof.
  intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 Q.
  Import naive_C_Rules.
  sepcon_assoc_change.
  tauto.
Qed.
Lemma mint_assoc8__user_auth_access : forall (A0 A1 A2 A3 A4 A5 A6 A7 Q : naive_C_Rules.expr),
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon A0 A1) A2) A3) A4) A5) A6) A7) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon A0 (naive_C_Rules.sepcon A1 (naive_C_Rules.sepcon A2 (naive_C_Rules.sepcon A3 (naive_C_Rules.sepcon A4 (naive_C_Rules.sepcon A5 (naive_C_Rules.sepcon A6 A7))))))) Q.
Proof.
  intros A0 A1 A2 A3 A4 A5 A6 A7 Q.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Hrefl.
  pose proof naive_C_Rules.logic_equiv_symm_instance as Hsymm.
  pose proof naive_C_Rules.logic_equiv_trans_instance as Htrans.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hder.
  naive_C_Rules.sepcon_right_assoc.
  auto.
Qed.
Lemma mint_assoc10__user_auth_access : forall (A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 Q : naive_C_Rules.expr),
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon (naive_C_Rules.sepcon A0 A1) A2) A3) A4) A5) A6) A7) A8) A9) Q ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon A0 (naive_C_Rules.sepcon A1 (naive_C_Rules.sepcon A2 (naive_C_Rules.sepcon A3 (naive_C_Rules.sepcon A4 (naive_C_Rules.sepcon A5 (naive_C_Rules.sepcon A6 (naive_C_Rules.sepcon A7 (naive_C_Rules.sepcon A8 A9))))))))) Q.
Proof.
  intros A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 Q.
  pose proof naive_C_Rules.logic_equiv_refl_instance as Hrefl.
  pose proof naive_C_Rules.logic_equiv_symm_instance as Hsymm.
  pose proof naive_C_Rules.logic_equiv_trans_instance as Htrans.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as Hsep.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as Hder.
  naive_C_Rules.sepcon_right_assoc.
  auto.
Qed.
Lemma find_set__core_success_result : forall h a b v,
  mint_find (mint_set h a v) b =
  option_map (fun c => if Z.eqb (mint_address c) a
    then mint_cell (mint_kind c) (mint_address c) (Some v) else c)
    (mint_find h b).
Proof.
  intros h a b v. unfold mint_find, mint_set.
  induction h as [|c h IH]; simpl; [reflexivity|].
  destruct (Z.eqb (mint_address c) a) eqn:Ha; simpl;
    destruct (Z.eqb (mint_address c) b) eqn:Hb; simpl; rewrite ?Ha; auto.
Qed.
Lemma value_set__core_success_result : forall h k a b v,
  mint_writable h k a ->
  mint_value (mint_set h a v) b =
  if Z.eqb b a then v else mint_value h b.
Proof.
  intros h k a b v Hw.
  destruct (Z.eqb b a) eqn:E.
  - apply Z.eqb_eq in E. subst b.
    destruct Hw as [old Hfind].
    unfold mint_value. rewrite find_set__core_success_result, Hfind.
    simpl. rewrite Z.eqb_refl. reflexivity.
  - unfold mint_value. rewrite find_set__core_success_result.
    destruct (mint_find h b) as [c|] eqn:Hfind; [|reflexivity].
    unfold mint_find in Hfind. apply find_some in Hfind.
    destruct Hfind as [_ Haddr]. apply Z.eqb_eq in Haddr.
    simpl. rewrite Haddr, E. reflexivity.
Qed.
Lemma updated_eq__core_success_result : forall h L d s f r,
  mint_writable h 0 (mint_dty L) ->
  mint_set (mint_set (mint_set h (mint_dty L) 1) (mint_dco L)
    (mint_value (mint_set h (mint_dty L) 1) (mint_sco L))) (mint_dri L) r =
  mint_updated h L d s f r.
Proof.
  intros h L d s f r Hw.
  rewrite (value_set__core_success_result h 0 (mint_dty L) (mint_sco L) 1 Hw).
  unfold mint_set, mint_updated. repeat rewrite map_map.
  apply map_ext. intros [k a old]. unfold mint_updated_cell. simpl.
  destruct (Z.eqb a (mint_dty L)); simpl;
    destruct (Z.eqb a (mint_dco L)); simpl;
    destruct (Z.eqb a (mint_dri L)); reflexivity.
Qed.
Lemma remove_absent__core_pointer_views : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c t IH]; intros a H; [reflexivity|].
  unfold mint_remove in *; simpl in *.
  destruct (Z.eqb (mint_address c) a) eqn:E.
  - apply Z.eqb_eq in E. exfalso. apply H. left. exact E.
  - simpl. f_equal. apply IH. intro Hin. apply H. right. exact Hin.
Qed.
Lemma find_factor__core_pointer_views : forall h c,
  NoDup (map mint_address h) -> mint_find h (mint_address c) = Some c ->
  naive_C_Rules.derivable1 (mint_heap h)
    (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h (mint_address c)))) /\
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h (mint_address c))))
    (mint_heap h).
Proof.
  Import naive_C_Rules.
  induction h as [|x t IH]; intros c Hnd Hf; [discriminate|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  unfold mint_find in Hf; simpl in Hf.
  destruct (Z.eqb (mint_address x) (mint_address c)) eqn:E.
  - inversion Hf; subst x.
    unfold mint_remove at 1 2; simpl. rewrite Z.eqb_refl. simpl.
    change ((mint_heap (c :: t) |-- mint_cell_heap c ** mint_heap (mint_remove t (mint_address c)))%sac /\
      (mint_cell_heap c ** mint_heap (mint_remove t (mint_address c)) |-- mint_heap (c :: t))%sac).
    rewrite (remove_absent__core_pointer_views t (mint_address c) Hnot).
    change ((mint_cell_heap c ** mint_heap t |-- mint_cell_heap c ** mint_heap t)%sac /\
      (mint_cell_heap c ** mint_heap t |-- mint_cell_heap c ** mint_heap t)%sac).
    split; cancel.
  - specialize (IH c Htail Hf) as [Hex Hput].
    unfold mint_remove at 1 2; simpl. rewrite E. simpl.
    change ((mint_cell_heap x ** mint_heap t |-- mint_cell_heap c **
      (mint_cell_heap x ** mint_heap (mint_remove t (mint_address c))))%sac /\
      (mint_cell_heap c ** (mint_cell_heap x ** mint_heap (mint_remove t (mint_address c)))
      |-- mint_cell_heap x ** mint_heap t)%sac).
    split.
    + sep_apply Hex. cancel.
    + sep_apply Hput. cancel.
Qed.
Lemma read_factor__core_pointer_views : forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1 (mint_heap h)
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
       (mint_heap (mint_remove h a))) /\
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
       (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  intros h k a [Hnd Hk] [v Hf].
  assert (Hv : mint_value h a = v) by (unfold mint_value; rewrite Hf; reflexivity).
  rewrite Hv. exact (find_factor__core_pointer_views h (mint_cell k a (Some v)) Hnd Hf).
Qed.
Lemma remove_absent__user_pointer_views : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c t IH]; intros a H; simpl in *; [reflexivity|].
  unfold mint_remove in *; simpl.
  assert (E : Z.eqb (mint_address c) a = false).
  { apply Z.eqb_neq. intro E; apply H; left; exact E. }
  rewrite E; simpl. f_equal. apply IH. tauto.
Qed.
Lemma factor_cell__user_pointer_views : forall h a c,
  NoDup (map mint_address h) -> mint_find h a = Some c ->
  naive_C_Rules.derivable1 (mint_heap h) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))) /\
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  pose proof naive_C_Rules.logic_equiv_sepcon_proper as logic_equiv_sepcon_proper_local.
  pose proof naive_C_Rules.logic_equiv_proper_derivable1 as logic_equiv_proper_derivable1_local.
  pose proof naive_C_Rules.derivable1_proper_derivable1 as derivable1_proper_derivable1_local.
  pose proof naive_C_Rules.derivable1s_sepcon_proper as derivable1s_sepcon_proper_local.
  pose proof naive_C_Rules.logic_equiv_refl_instance as logic_equiv_refl_instance_local.
  pose proof naive_C_Rules.logic_equiv_symm_instance as logic_equiv_symm_instance_local.
  pose proof naive_C_Rules.logic_equiv_trans_instance as logic_equiv_trans_instance_local.
  pose proof naive_C_Rules.derivable1_refl_instance as derivable1_refl_instance_local.
  induction h as [|x t IH]; intros a c Hnd Hfind; [discriminate|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  unfold mint_find in Hfind; simpl in Hfind.
  destruct (Z.eqb (mint_address x) a) eqn:E.
  - inversion Hfind; subst c. apply Z.eqb_eq in E; subst a.
    assert (R : mint_remove (x :: t) (mint_address x) = t).
    { unfold mint_remove; simpl. rewrite Z.eqb_refl; simpl.
      change (mint_remove t (mint_address x) = t).
      apply remove_absent__user_pointer_views; exact Hnot. }
    rewrite R. cbn [mint_heap fold_right]; fold (mint_heap t); fold (mint_heap (mint_remove t (mint_address x))).
    split; naive_C_Rules.sepcon_cancel.
  - assert (R : mint_remove (x :: t) a = x :: mint_remove t a).
    { unfold mint_remove; simpl; rewrite E; reflexivity. }
    rewrite R. specialize (IH a c Htail Hfind). destruct IH as [F B].
    cbn [mint_heap fold_right]; fold (mint_heap t); fold (mint_heap (mint_remove t a)).
    split.
    + naive_C_Rules.sep_apply F. naive_C_Rules.sepcon_cancel.
    + naive_C_Rules.sep_apply B. naive_C_Rules.sepcon_cancel.
Qed.
Lemma read_factor__user_pointer_views : forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1 (mint_heap h) (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a)))) (mint_heap (mint_remove h a))) /\
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a)))) (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  intros h k a [N K] [v F]. unfold mint_value; rewrite F; simpl.
  apply factor_cell__user_pointer_views; assumption.
Qed.
Lemma find_remove__user_pointer_views : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  induction h as [|c t IH]; intros a b H; [reflexivity|].
  unfold mint_find, mint_remove in *; simpl.
  destruct (Z.eqb (mint_address c) b) eqn:B; simpl.
  - assert (A : Z.eqb (mint_address c) a = false).
    { apply Z.eqb_neq. apply Z.eqb_eq in B. congruence. }
    rewrite A. apply IH; exact H.
  - simpl. destruct (Z.eqb (mint_address c) a); [reflexivity|].
    apply IH; exact H.
Qed.
Lemma remove_wf__user_pointer_views : forall h a,
  mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
  induction h as [|c t IH]; intros a [N K].
  - split; constructor.
  - inversion N as [|? ? Hnot Nt]; subst.
    inversion K as [|? ? Hkind Kt]; subst.
    specialize (IH a (conj Nt Kt)). unfold mint_remove; simpl.
    destruct (negb (Z.eqb (mint_address c) a)) eqn:E; [|exact IH].
    destruct IH as [Ni Ki]. split; constructor; auto.
    intro H. apply Hnot. apply in_map_iff in H.
    destruct H as [d [Hd Hin]]. apply filter_In in Hin.
    apply in_map_iff. exists d. tauto.
Qed.
Lemma remove_reads__user_pointer_views : forall h k a b,
  a <> b -> mint_readable h k a ->
  mint_readable (mint_remove h b) k a /\
  mint_value (mint_remove h b) a = mint_value h a.
Proof.
  intros h k a b H R. split.
  - destruct R as [v F]. exists v.
    rewrite find_remove__user_pointer_views; assumption.
  - unfold mint_value. rewrite find_remove__user_pointer_views by exact H.
    reflexivity.
Qed.
Lemma different_kinds__user_pointer_views : forall h k j a b,
  k <> j -> mint_readable h k a -> mint_readable h j b -> a <> b.
Proof.
  intros h k j a b K [v F] [w G] E; subst b.
  rewrite F in G. inversion G. contradiction.
Qed.
Lemma absent_remove__core_store_views : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c t IH]; intros a H; simpl; auto.
  unfold mint_remove in *; simpl in *.
  destruct (Z.eqb (mint_address c) a) eqn:E; simpl.
  - apply Z.eqb_eq in E. exfalso. apply H. left. exact E.
  - f_equal. apply IH. tauto.
Qed.
Lemma absent_set__core_store_views : forall h a v,
  ~ In a (map mint_address h) -> mint_set h a v = h.
Proof.
  induction h as [|c t IH]; intros a v H; simpl; auto.
  unfold mint_set in *; simpl in *.
  destruct (Z.eqb (mint_address c) a) eqn:E; simpl.
  - apply Z.eqb_eq in E. exfalso. apply H. left. exact E.
  - f_equal. apply IH. tauto.
Qed.
Lemma write_factor__core_store_views : forall h a,
  mint_wellformed h -> mint_writable h 0 a ->
  naive_C_Rules.derivable1 (mint_heap h) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mint_heap (mint_remove h a))).
Proof.
  Import naive_C_Rules.
  induction h as [|c t IH]; intros a [ND WF] [old F].
  - discriminate F.
  - inversion ND as [|? ? Hnot ND']; subst.
    inversion WF as [|? ? Wc WF']; subst.
    unfold mint_find in F; simpl in F.
    destruct (Z.eqb (mint_address c) a) eqn:E.
    + inversion F; subst c. simpl in Hnot.
      unfold mint_remove; simpl. rewrite Z.eqb_refl. simpl.
      change (naive_C_Rules.derivable1 (mint_heap (mint_cell 0 a old :: t)) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mint_heap (mint_remove t a)))).
      rewrite absent_remove__core_store_views by exact Hnot.
      unfold mint_heap at 1; simpl; fold (mint_heap t).
      destruct old as [v|]; cbn [mint_cell_heap].
      * sep_apply_l_atomic (naive_C_Rules.store_uint_undef_store_uint a v).
        cancel (naive_C_Rules.undef_store_uint a). cancel.
      * cancel (naive_C_Rules.undef_store_uint a). cancel.
    + unfold mint_remove; simpl; rewrite E; simpl.
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap t)) (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove t a))))).
      sep_apply_l_atomic (IH a (conj ND' WF') (ex_intro _ old F)).
      cancel (mint_cell_heap c). cancel.
Qed.
Lemma write_restore__core_store_views : forall h a v,
  mint_wellformed h -> mint_writable h 0 a ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mint_heap (mint_remove h a))) (mint_heap (mint_set h a v)).
Proof.
  Import naive_C_Rules.
  induction h as [|c t IH]; intros a v [ND WF] [old F].
  - discriminate F.
  - inversion ND as [|? ? Hnot ND']; subst.
    inversion WF as [|? ? Wc WF']; subst.
    unfold mint_find in F; simpl in F.
    destruct (Z.eqb (mint_address c) a) eqn:E.
    + inversion F; subst c. simpl in Hnot.
      unfold mint_remove, mint_set; simpl; rewrite Z.eqb_refl; simpl.
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mint_heap (mint_remove t a))) (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (mint_heap (mint_set t a v)))).
      rewrite absent_remove__core_store_views, absent_set__core_store_views by exact Hnot.
      cancel (naive_C_Rules.store_uint a v). cancel.
    + unfold mint_remove, mint_set; simpl; rewrite E; simpl.
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a v) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove t a)))) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_set t a v)))).
      sep_apply_l_atomic (IH a v (conj ND' WF') (ex_intro _ old F)).
      cancel (mint_cell_heap c). cancel.
Qed.
Lemma remove_absent__core_copy h a :
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c h IH]; intros H; simpl; auto.
  unfold mint_remove in *; simpl.
  assert (E : Z.eqb (mint_address c) a = false).
  { apply Z.eqb_neq. intros E. apply H. simpl. auto. }
  rewrite E. simpl. f_equal. apply IH. intros F. apply H. simpl. auto.
Qed.
Lemma set_absent__core_copy h a v :
  ~ In a (map mint_address h) -> mint_set h a v = h.
Proof.
  induction h as [|c h IH]; intros H; simpl; auto.
  unfold mint_set in *; simpl.
  assert (E : Z.eqb (mint_address c) a = false).
  { apply Z.eqb_neq. intros E. apply H. simpl. auto. }
  rewrite E. f_equal. apply IH. intros F. apply H. simpl. auto.
Qed.
Lemma find_remove__core_copy h a b : a <> b ->
 mint_find (mint_remove h b) a = mint_find h a.
Proof.
 Import naive_C_Rules.
 Local Open Scope sac.
 induction h as [|c h IH]; intros N; [reflexivity|].
 unfold mint_find, mint_remove in *; simpl.
 destruct (Z.eqb (mint_address c) b) eqn:E; simpl.
 - apply Z.eqb_eq in E. subst b.
   assert (F : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; congruence).
   rewrite F. apply IH; assumption.
 - simpl. destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_wf__core_copy h a : mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
 induction h as [|c h IH]; intros [N K]; [split; constructor|].
 inversion N; inversion K; subst.
 unfold mint_remove; simpl. destruct (Z.eqb (mint_address c) a); simpl.
 - apply IH; split; assumption.
 - destruct (IH (conj H2 H6)) as [N' K']. split; constructor; auto.
   intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as [x [Ex Ix]].
   apply filter_In in Ix. apply in_map_iff. exists x. tauto.
Qed.
Lemma set_wf__core_copy h a v : mint_wellformed h -> mint_wellformed (mint_set h a v).
Proof.
 intros [N K]. split.
 - unfold mint_set. rewrite map_map.
   replace (map (fun x : MintCell => mint_address (if Z.eqb (mint_address x) a then mint_cell (mint_kind x) (mint_address x) (Some v) else x)) h) with (map mint_address h).
   + exact N.
   + apply map_ext. intros x. destruct (Z.eqb (mint_address x) a); reflexivity.
 - unfold mint_set. apply Forall_map. eapply Forall_impl; [|exact K].
   intros c H. destruct (Z.eqb (mint_address c) a); exact H.
Qed.
Lemma set_find__core_copy h a b v :
 mint_find (mint_set h a v) b =
 option_map (fun c => if Z.eqb (mint_address c) a then mint_cell (mint_kind c) (mint_address c) (Some v) else c) (mint_find h b).
Proof.
 induction h as [|c h IH]; [reflexivity|].
 unfold mint_find, mint_set in *; simpl.
 destruct (Z.eqb (mint_address c) a) eqn:E; simpl;
 destruct (Z.eqb (mint_address c) b); simpl; try rewrite E; auto.
Qed.
Lemma set_writable__core_copy h k b a v :
 mint_writable h k b -> mint_writable (mint_set h a v) k b.
Proof.
 intros [w H]. unfold mint_writable. rewrite set_find__core_copy, H. simpl.
 destruct (Z.eqb b a); eexists; reflexivity.
Qed.
Lemma factor__core_copy h k a w :
 NoDup (map mint_address h) -> mint_find h a = Some (mint_cell k a w) ->
 naive_C_Rules.derivable1 (mint_heap h) (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a w)) (mint_heap (mint_remove h a))).
Proof.
 Import naive_C_Rules.
 Local Open Scope sac.
 induction h as [|c h IH]; intros N F; [discriminate|].
 inversion N as [|? ? Hnot N']; subst.
 unfold mint_find in F; simpl in F.
 destruct (Z.eqb (mint_address c) a) eqn:E.
 - inversion F; subst c. unfold mint_remove; simpl. rewrite Z.eqb_refl; simpl.
   fold (mint_remove h a).
   rewrite (remove_absent__core_copy h a Hnot). unfold mint_heap; simpl. cancel.
 - unfold mint_remove; simpl. rewrite E; simpl. fold (mint_remove h a).
   change (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap h) |--
      naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a w))
        (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))))%sac.
   sep_apply_l_atomic (IH N' F). cancel.
Qed.
Lemma restore__core_copy h k a w :
 NoDup (map mint_address h) -> mint_find h a = Some (mint_cell k a w) ->
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a w)) (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
 Import naive_C_Rules.
 Local Open Scope sac.
 induction h as [|c h IH]; intros N F; [discriminate|].
 inversion N as [|? ? Hnot N']; subst.
 unfold mint_find in F; simpl in F.
 destruct (Z.eqb (mint_address c) a) eqn:E.
 - inversion F; subst c. unfold mint_remove; simpl. rewrite Z.eqb_refl; simpl.
   fold (mint_remove h a).
   rewrite (remove_absent__core_copy h a Hnot). unfold mint_heap; simpl. cancel.
 - unfold mint_remove; simpl. rewrite E; simpl. fold (mint_remove h a).
   change (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a w))
       (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))) |--
       naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap h))%sac.
   sep_apply_r_atomic (IH N' F). cancel. cancel (mint_cell_heap (mint_cell k a w)).
Qed.
Lemma write_restore__core_copy h k a v :
 NoDup (map mint_address h) -> mint_writable h k a ->
 naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap (mint_remove h a))) (mint_heap (mint_set h a v)).
Proof.
 Import naive_C_Rules.
 Local Open Scope sac.
 induction h as [|c h IH]; intros N [w F]; [discriminate|].
 inversion N as [|? ? Hnot N']; subst.
 unfold mint_find in F; simpl in F.
 destruct (Z.eqb (mint_address c) a) eqn:E.
 - inversion F; subst c. unfold mint_remove, mint_set; simpl. rewrite Z.eqb_refl; simpl.
   fold (mint_remove h a) (mint_set h a v).
   rewrite (remove_absent__core_copy h a Hnot), (set_absent__core_copy h a v Hnot).
   unfold mint_heap; simpl. cancel.
 - unfold mint_remove, mint_set; simpl. rewrite E; simpl. fold (mint_remove h a) (mint_set h a v).
   change (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v)))
       (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))) |--
       naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_set h a v)))%sac.
   sep_apply_r_atomic (IH N' (ex_intro _ w F)). cancel. cancel (mint_cell_heap (mint_cell k a (Some v))).
Qed.
Lemma read_find__core_copy h k a : mint_readable h k a ->
 mint_find h a = Some (mint_cell k a (Some (mint_value h a))).
Proof.
 intros [v F]. unfold mint_value. rewrite F. reflexivity.
Qed.
Lemma read_factor__core_copy h a : mint_wellformed h -> mint_readable h 0 a ->
 naive_C_Rules.derivable1 (mint_heap h)
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mint_value h a)) (mint_heap (mint_remove h a))).
Proof.
 intros [N K] R. exact (factor__core_copy h 0 a (Some (mint_value h a)) N (read_find__core_copy h 0 a R)).
Qed.
Lemma write_factor__core_copy h a : mint_wellformed h -> mint_writable h 0 a ->
 naive_C_Rules.derivable1 (mint_heap h)
 (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint a) (mint_heap (mint_remove h a))).
Proof.
 Import naive_C_Rules. Local Open Scope sac.
 intros [N K] [w F]. sep_apply_l_atomic (factor__core_copy h 0 a w N F).
 destruct w as [v|]; cbn [mint_cell_heap mint_kind mint_initial mint_address].
 - sep_apply_l_atomic (store_uint_undef_store_uint a v). cancel.
 - cancel.
Qed.
Lemma remove_commute__core_copy h a b :
 mint_remove (mint_remove h a) b = mint_remove (mint_remove h b) a.
Proof.
 induction h as [|c h IH]; [reflexivity|]. unfold mint_remove in *; simpl.
 destruct (Z.eqb (mint_address c) a) eqn:E;
 destruct (Z.eqb (mint_address c) b) eqn:F; simpl; rewrite ?E, ?F; simpl; congruence.
Qed.
Lemma copy_restore__core_copy h s d : mint_wellformed h ->
 mint_readable h 0 s -> mint_writable h 0 d -> s <> d ->
 naive_C_Rules.derivable1
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint s (mint_value h s))
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint d (mint_value h s))
 (mint_heap (mint_remove (mint_remove h s) d))))
 (mint_heap (mint_set h d (mint_value h s))).
Proof.
 Import naive_C_Rules. Local Open Scope sac.
 intros W R D N.
 pose proof (remove_wf__core_copy h d W) as W'.
 pose proof (read_find__core_copy h 0 s R) as F.
 assert (F' : mint_find (mint_remove h d) s = Some (mint_cell 0 s (Some (mint_value h s)))).
 { rewrite find_remove__core_copy; assumption. }
 sep_apply_r_atomic (write_restore__core_copy h 0 d (mint_value h s) (proj1 W) D).
 rewrite (remove_commute__core_copy h s d).
 sep_apply_r_atomic (restore__core_copy (mint_remove h d) 0 s (Some (mint_value h s)) (proj1 W') F').
 cbn [mint_cell_heap mint_kind mint_initial mint_address]. cancel. cancel (store_uint s (mint_value h s)).
Qed.
Lemma access_copy__core_copy h L d s f r :
 mint_core_pre h L d s f r -> mint_eligible h L d s f r ->
 mint_wellformed (mint_set h (mint_dty L) 1) /\
 mint_readable (mint_set h (mint_dty L) 1) 0 (mint_sco L) /\
 mint_writable (mint_set h (mint_dty L) 1) 0 (mint_dco L).
Proof.
 intros [W [_ [_ [_ [_ A]]]]] E.
 pose proof E as [P [D [S _]]].
 specialize (A P). destruct A as [_ [_ A]].
 specialize (A (conj D S)). destruct A as [_ [_ A]]. specialize (A E).
 destruct A as [R [T [C Q]]]. split.
 - apply set_wf__core_copy; exact W.
 - split; [exact R|apply set_writable__core_copy; exact C].
Qed.
Lemma copy_factor__core_copy h s d : mint_wellformed h ->
 mint_readable h 0 s -> mint_writable h 0 d -> s <> d ->
 naive_C_Rules.derivable1 (mint_heap h)
 (naive_C_Rules.sepcon (naive_C_Rules.store_uint s (mint_value h s))
 (naive_C_Rules.sepcon (naive_C_Rules.undef_store_uint d)
 (mint_heap (mint_remove (mint_remove h s) d)))).
Proof.
 Import naive_C_Rules. Local Open Scope sac.
 intros W R [w D] N.
 assert (D' : mint_writable (mint_remove h s) 0 d).
 { exists w. rewrite find_remove__core_copy; [exact D|congruence]. }
 sep_apply_l_atomic (read_factor__core_copy h s W R).
 sep_apply_l_atomic (write_factor__core_copy (mint_remove h s) d (remove_wf__core_copy h s W) D').
 cancel.
Qed.
Lemma mask32__core_rights_transition : forall old r,
  0 <= r < 2^32 ->
  Z.land (Z.lnot old) r = Z.land (Z.lxor old (2^32-1)) r.
Proof.
  intros old r Hr. apply Z.bits_inj. intros n.
  destruct (Z_lt_ge_dec n 0) as [Hn|Hn].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - rewrite !Z.land_spec, Z.lnot_spec, Z.lxor_spec by lia.
    destruct (Z_lt_ge_dec n 32) as [Hlow|Hhigh].
    + replace (2^32-1) with (Z.ones 32) by reflexivity.
      rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit old n), (Z.testbit r n); reflexivity.
    + assert (Hb : Z.testbit r n = false).
      { rewrite <- (Z.mod_small r (2^32)) by exact Hr.
        apply Z.mod_pow2_bits_high. lia. }
      rewrite Hb, !andb_false_r. reflexivity.
Qed.
Lemma remove_absent__core_rights_transition : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c h IH]; intros a H; simpl in *; auto.
  unfold mint_remove in *. simpl.
  assert (E : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; tauto).
  rewrite E. simpl. f_equal. apply IH. tauto.
Qed.
Lemma find_remove__core_rights_transition : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  induction h as [|c h IH]; intros a b H; simpl; auto.
  unfold mint_find, mint_remove in *. simpl.
  destruct (Z.eqb (mint_address c) b) eqn:Eb; simpl.
  - apply Z.eqb_eq in Eb.
    assert (Ea : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; congruence).
    rewrite Ea. apply IH. exact H.
  - destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_reads__core_rights_transition : forall h k a b,
  a <> b -> mint_readable h k a -> mint_readable (mint_remove h b) k a /\
  mint_value (mint_remove h b) a = mint_value h a.
Proof.
  intros h k a b H R. unfold mint_readable, mint_value in *.
  rewrite find_remove__core_rights_transition by exact H. auto.
Qed.
Lemma remove_wf__core_rights_transition : forall h a,
  mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
  intros h a [N F]. split.
  - induction h as [|c h IH]; simpl in *; [constructor|].
    inversion N; subst. unfold mint_remove in *. simpl.
    destruct (negb (Z.eqb (mint_address c) a)); simpl.
    + constructor.
      * intros Hin. apply in_map_iff in Hin. destruct Hin as [x [E Hx]].
        apply filter_In in Hx. apply H1. rewrite <- E. apply in_map. tauto.
      * apply IH; auto. inversion F; auto.
    + apply IH; auto. inversion F; auto.
  - unfold mint_remove. apply Forall_forall. intros c Hc.
    apply filter_In in Hc. rewrite Forall_forall in F. apply F. tauto.
Qed.
Lemma read_factor__core_rights_transition : forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a)))) (mint_heap (mint_remove h a)))
    (mint_heap h).
Proof.
  Import naive_C_Rules.
  induction h as [|c h IH]; intros k a [N F] [v R].
  - discriminate R.
  - inversion N as [|? ? Hnot Ntail]; subst.
    inversion F as [|? ? Fc Ftail]; subst.
    unfold mint_find in R. simpl in R.
    destruct (Z.eqb (mint_address c) a) eqn:E.
    + inversion R; subst c. simpl in *.
      assert (Rem : mint_remove h a = h) by (apply remove_absent__core_rights_transition; exact Hnot).
      unfold mint_remove at 1. simpl. rewrite Z.eqb_refl. simpl.
      fold (mint_remove h a). rewrite Rem.
      unfold mint_value, mint_find. simpl. rewrite Z.eqb_refl. simpl.
      cancel.
    + assert (V : mint_value (c :: h) a = mint_value h a).
      { unfold mint_value, mint_find. simpl. rewrite E. reflexivity. }
      rewrite V. unfold mint_remove at 1. simpl. rewrite E. simpl.
      fold (mint_remove h a).
      change (naive_C_Rules.derivable1
        (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
          (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))))
        (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap h))).
      sep_apply_l_atomic (IH k a (conj Ntail Ftail) (ex_intro _ v R)).
      cancel.
Qed.
Lemma read_two__core_rights_transition : forall h a b,
  mint_wellformed h -> mint_readable h 0 a -> mint_readable h 0 b -> a <> b ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon
      (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mint_value h a))
                           (naive_C_Rules.store_uint b (mint_value h b)))
      (mint_heap (mint_remove (mint_remove h a) b)))
    (mint_heap h).
Proof.
  Import naive_C_Rules.
  intros h a b WF Ra Rb NE.
  destruct (remove_reads__core_rights_transition h 0 b a ltac:(lia) Rb) as [Rb' Vb].
  pose proof (read_factor__core_rights_transition (mint_remove h a) 0 b
    (remove_wf__core_rights_transition h a WF) Rb') as F.
  cbn [mint_cell_heap mint_kind mint_initial mint_address] in F.
  rewrite Vb in F.
  sep_apply_l_atomic F.
  pose proof (read_factor__core_rights_transition h 0 a WF Ra) as G.
  cbn [mint_cell_heap mint_kind mint_initial mint_address] in G.
  sep_apply_l_atomic G.
  cancel.
Qed.
Lemma associate__core_rights_transition : forall P Q R S,
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (naive_C_Rules.sepcon P Q) R) S ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon P (naive_C_Rules.sepcon Q R)) S.
Proof.
  Import naive_C_Rules.
  intros P Q R S H.
  sep_apply_r_atomic H.
  sepcon_assoc_change.
  cancel.
Qed.
Lemma mask32__core_rights_results : forall old r,
  0 <= r < 2^32 ->
  Z.land (Z.lnot old) r = Z.land (Z.lxor old 4294967295) r.
Proof.
  intros old r Hr. apply Z.bits_inj. intro n.
  destruct (Z_lt_ge_dec n 0) as [Hn|Hn].
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - rewrite !Z.land_spec, Z.lnot_spec, Z.lxor_spec by lia.
    destruct (Z_lt_ge_dec n 32) as [Hlo|Hhi].
    + change 4294967295 with (Z.ones 32).
      rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit old n), (Z.testbit r n); reflexivity.
    + assert (E : Z.testbit r n = false).
      { rewrite <- (unsigned_last_nbits_eq r 32 Hr).
        apply Ztestbits_unsigned_high. lia. }
      rewrite E. now rewrite !Bool.andb_false_r.
Qed.
Lemma remove_absent__core_rights_results : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c h IH]; intros a H; simpl; auto.
  unfold mint_remove in *. simpl in *.
  assert (E : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; intuition).
  rewrite E. simpl. f_equal. apply IH. intuition.
Qed.
Lemma restore_find__core_rights_results : forall h k a v,
  NoDup (map mint_address h) ->
  mint_find h a = Some (mint_cell k a (Some v)) ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v)))
      (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  Import naive_C_Rules.
  induction h as [|c h IH]; intros k a v Hnd Hfind; [discriminate|].
  inversion Hnd as [|x xs Hnot Htail]; subst.
  unfold mint_find in Hfind. simpl in Hfind.
  unfold mint_remove at 1. simpl.
  destruct (Z.eqb (mint_address c) a) eqn:E.
  - inversion Hfind; subst c. simpl.
    fold (mint_remove h a).
    rewrite (remove_absent__core_rights_results h a Hnot).
    unfold mint_heap at 2. simpl. fold (mint_heap h). cancel.
  - simpl. change (mint_heap (c :: mint_remove h a)) with
      (sepcon (mint_cell_heap c) (mint_heap (mint_remove h a))).
    change (mint_heap (c :: h)) with (sepcon (mint_cell_heap c) (mint_heap h)).
    pose proof (IH k a v Htail Hfind) as HH.
    cbn [mint_cell_heap mint_kind mint_initial mint_address] in HH.
    fold (mint_remove h a). cancel (mint_cell_heap c). exact HH.
Qed.
Lemma read_factor__core_rights_results : forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
      (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  intros h k a [Hnd _] [v E].
  unfold mint_value. rewrite E. simpl.
  exact (restore_find__core_rights_results h k a v Hnd E).
Qed.
Lemma remove_find__core_rights_results : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  induction h as [|c h IH]; intros a b H; simpl; auto.
  unfold mint_find, mint_remove in *. simpl.
  destruct (Z.eqb (mint_address c) b) eqn:Eb; simpl.
  - apply Z.eqb_eq in Eb.
    assert (Ea : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; congruence).
    rewrite Ea. apply IH. exact H.
  - simpl. destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_wf__core_rights_results : forall h a,
  mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
  intros h a [Hnd Hk]. split.
  - unfold mint_remove. induction h as [|c h IH]; simpl in *; auto.
    inversion Hnd; subst. destruct (negb (Z.eqb (mint_address c) a)); simpl.
    + constructor.
      * intro Hin. apply H1. apply in_map_iff in Hin.
        destruct Hin as [x [Ex Hx]]. apply filter_In in Hx.
        apply in_map_iff. exists x. tauto.
      * apply IH; auto. inversion Hk; auto.
    + apply IH; auto. inversion Hk; auto.
  - unfold mint_remove. apply Forall_forall. intros c Hc.
    apply filter_In in Hc. rewrite Forall_forall in Hk. apply Hk. exact (proj1 Hc).
Qed.
Lemma restore_uint__core_rights_results : forall h a,
 mint_wellformed h -> mint_readable h 0 a ->
 naive_C_Rules.derivable1
  (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mint_value h a))
   (mint_heap (mint_remove h a))) (mint_heap h).
Proof. intros. exact (read_factor__core_rights_results h 0 a H H0). Qed.
Lemma restore_two_uint__core_rights_results : forall h a b,
 mint_wellformed h -> mint_readable h 0 a -> mint_readable h 0 b -> a <> b ->
 naive_C_Rules.derivable1
  (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mint_value h a))
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint b (mint_value h b))
    (mint_heap (mint_remove (mint_remove h a) b)))) (mint_heap h).
Proof.
 Import naive_C_Rules.
 intros h a b Hwf Ha Hb Hab.
 assert (Hr : mint_readable (mint_remove h a) 0 b).
 { unfold mint_readable in *. rewrite remove_find__core_rights_results by congruence. exact Hb. }
 pose proof (restore_uint__core_rights_results (mint_remove h a) b
   (remove_wf__core_rights_results h a Hwf) Hr) as HH.
 unfold mint_value at 1 in HH.
 rewrite remove_find__core_rights_results in HH by congruence.
 fold (mint_value h b) in HH.
 sep_apply_l_atomic HH.
 sep_apply_l_atomic (restore_uint__core_rights_results h a Hwf Ha). cancel.
Qed.
Lemma remove_absent__core_read_results : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  induction h as [|c t IH]; intros a H; simpl; auto.
  unfold mint_remove in *; simpl in *.
  assert (E : Z.eqb (mint_address c) a = false).
  { apply Z.eqb_neq; intro; apply H; left; assumption. }
  rewrite E; simpl; f_equal; apply IH; tauto.
Qed.
Lemma restore_read__core_read_results : forall h k a,
  NoDup (map mint_address h) -> mint_readable h k a ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a))))
       (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  induction h as [|c t IH]; intros k a ND [v F]; [discriminate|].
  inversion ND as [|? ? Hnot ND']; subst.
  unfold mint_find in F; simpl in F.
  destruct (Z.eqb (mint_address c) a) eqn:E.
  - inversion F; subst c.
    assert (R : mint_remove t a = t).
    { apply remove_absent__core_read_results; exact Hnot. }
    unfold mint_value, mint_find, mint_remove, mint_heap; simpl.
    rewrite Z.eqb_refl; simpl.
    change (naive_C_Rules.derivable1
      (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v)))
        (mint_heap (mint_remove t a)))
      (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap t))).
    rewrite R; cancel.
  - assert (V : mint_value (c :: t) a = mint_value t a).
    { unfold mint_value, mint_find; simpl; rewrite E; reflexivity. }
    assert (R : mint_remove (c :: t) a = c :: mint_remove t a).
    { unfold mint_remove; simpl; rewrite E; reflexivity. }
    rewrite V, R.
    change ((mint_cell_heap (mint_cell k a (Some (mint_value t a))) **
       (mint_cell_heap c ** mint_heap (mint_remove t a))) |--
       (mint_cell_heap c ** mint_heap t))%sac.
    sep_apply_l_atomic (IH k a ND' (ex_intro _ v F)).
    cancel.
Qed.
Lemma remove_find__core_read_results : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  induction h as [|c t IH]; intros a b NE; simpl; auto.
  unfold mint_find, mint_remove in *; simpl.
  destruct (Z.eqb (mint_address c) b) eqn:E; simpl.
  - apply Z.eqb_eq in E.
    assert (A : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; congruence).
    rewrite A; apply IH; exact NE.
  - simpl; destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_nodup__core_read_results : forall h a,
  NoDup (map mint_address h) -> NoDup (map mint_address (mint_remove h a)).
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  induction h as [|c t IH]; intros a H; [constructor|].
  inversion H as [|? ? Hnot ND]; subst.
  unfold mint_remove; simpl.
  destruct (Z.eqb (mint_address c) a); simpl; [apply IH; exact ND|].
  constructor; [|apply IH; exact ND].
  intro Hin; apply in_map_iff in Hin; destruct Hin as [x [EQ Hin]].
  apply filter_In in Hin; apply Hnot; apply in_map_iff; exists x; tauto.
Qed.
Lemma restore_two__core_read_results : forall h a b,
  NoDup (map mint_address h) -> mint_readable h 0 a -> mint_readable h 0 b ->
  a <> b ->
  naive_C_Rules.derivable1
   (naive_C_Rules.sepcon (naive_C_Rules.store_uint a (mint_value h a))
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint b (mint_value h b))
      (mint_heap (mint_remove (mint_remove h a) b)))) (mint_heap h).
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  intros h a b ND RA RB NE.
  assert (F : mint_find (mint_remove h a) b = mint_find h b).
  { apply remove_find__core_read_results; congruence. }
  assert (V : mint_value (mint_remove h a) b = mint_value h b).
  { unfold mint_value; rewrite F; reflexivity. }
  assert (R : mint_readable (mint_remove h a) 0 b).
  { destruct RB as [v RB]; exists v; rewrite F; exact RB. }
  pose proof (restore_read__core_read_results (mint_remove h a) 0 b
    (remove_nodup__core_read_results h a ND) R) as HB.
  cbn [mint_cell_heap mint_kind mint_initial mint_address] in HB.
  rewrite V in HB.
  sep_apply_l_atomic HB.
  pose proof (restore_read__core_read_results h 0 a ND RA) as HA.
  cbn [mint_cell_heap mint_kind mint_initial mint_address] in HA.
  sep_apply_l_atomic HA. cancel.
Qed.
Lemma core_reads__core_read_results : forall h L d s f r,
  mint_core_pre h L d s f r ->
  unsigned_last_nbits d 32 < 64 -> unsigned_last_nbits s 32 < 64 ->
  0 <= f -> f <= 16 -> mint_dst h L <> 0 -> mint_src h L <> 0 ->
  NoDup (map mint_address h) /\ mint_readable h 0 (mint_sty L) /\
  (mint_value h (mint_sty L) = 1 -> mint_readable h 0 (mint_sri L)).
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  intros h L d s f r [WF [D [S [F [R A]]]]] BD BS BF TF NZD NZS.
  unfold mint_u8 in D, S.
  rewrite unsigned_last_nbits_eq in BD by (split; lia).
  rewrite unsigned_last_nbits_eq in BS by (split; lia).
  assert (V : mint_parameters_valid d s f) by (unfold mint_parameters_valid; lia).
  destruct (A V) as [_ [_ B]].
  destruct (B (conj NZD NZS)) as [RT [RR _]].
  destruct WF as [ND WF]. tauto.
Qed.
Lemma remove_absent__core_source_view : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c t IH]; intros a H; simpl; auto.
  unfold mint_remove in *; simpl in *.
  assert (mint_address c <> a) as E by intuition.
  rewrite (proj2 (Z.eqb_neq _ _) E); simpl.
  f_equal. apply IH. intuition.
Qed.
Lemma find_remove__core_source_view : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  induction h as [|c t IH]; intros a b H; auto.
  unfold mint_find, mint_remove in *; simpl.
  destruct (Z.eqb (mint_address c) b) eqn:E; simpl.
  - apply Z.eqb_eq in E.
    assert (mint_address c <> a) as N by congruence.
    rewrite (proj2 (Z.eqb_neq _ _) N). apply IH; auto.
  - simpl. destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_reads__core_source_view : forall h k a b,
  a <> b -> mint_readable h k a ->
  mint_readable (mint_remove h b) k a /\
  mint_value (mint_remove h b) a = mint_value h a.
Proof.
  intros h k a b N [v H]. unfold mint_readable, mint_value.
  rewrite find_remove__core_source_view by exact N.
  split; eauto.
Qed.
Lemma remove_wf__core_source_view : forall h a,
  mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
  induction h as [|c t IH]; intros a [HN HK].
  - split; constructor.
  - inversion HN as [|x xs Hnot Htail]; subst.
    inversion HK as [|x xs Hkind Hkinds]; subst.
    specialize (IH a (conj Htail Hkinds)).
    unfold mint_remove; simpl.
    destruct (Z.eqb (mint_address c) a) eqn:E; simpl.
    + exact IH.
    + destruct IH as [IN IK]. split; constructor; auto.
      intro C. apply Hnot. apply in_map_iff in C.
      destruct C as [d [D C]]. apply filter_In in C.
      apply in_map_iff. exists d; tauto.
Qed.
Lemma remove_absent__user_auth_views : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c h IH]; intros a H; simpl; auto.
  unfold mint_remove in *; simpl in *.
  assert (E : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; intuition).
  rewrite E; simpl. f_equal. apply IH. intuition.
Qed.
Lemma read_cell__user_auth_views : forall h k a,
  mint_readable h k a -> mint_find h a = Some (mint_cell k a (Some (mint_value h a))).
Proof.
  intros h k a [v H]. unfold mint_value. rewrite H. reflexivity.
Qed.
Lemma extract__user_auth_views : forall h c,
  NoDup (map mint_address h) -> mint_find h (mint_address c) = Some c ->
  naive_C_Rules.derivable1 (mint_heap h)
    (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h (mint_address c)))).
Proof.
  Import naive_C_Rules.
  induction h as [|x h IH]; intros c Hnd Hf; [discriminate|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  unfold mint_find in Hf; simpl in Hf.
  destruct (Z.eqb (mint_address x) (mint_address c)) eqn:E.
  - inversion Hf; subst x. unfold mint_remove; simpl. rewrite Z.eqb_refl. simpl.
    change (filter (fun x => negb (Z.eqb (mint_address x) (mint_address c))) h)
      with (mint_remove h (mint_address c)).
    rewrite remove_absent__user_auth_views by exact Hnot.
    cbn [mint_heap]. cancel.
  - unfold mint_remove; simpl. rewrite E; simpl.
    change (filter (fun x => negb (Z.eqb (mint_address x) (mint_address c))) h)
      with (mint_remove h (mint_address c)).
    cbn [mint_heap].
    sep_apply_l_atomic (IH c Htail Hf). cancel.
Qed.
Lemma restore__user_auth_views : forall h c,
  NoDup (map mint_address h) -> mint_find h (mint_address c) = Some c ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove h (mint_address c))))
    (mint_heap h).
Proof.
  Import naive_C_Rules.
  induction h as [|x h IH]; intros c Hnd Hf; [discriminate|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  unfold mint_find in Hf; simpl in Hf.
  destruct (Z.eqb (mint_address x) (mint_address c)) eqn:E.
  - inversion Hf; subst x. unfold mint_remove; simpl. rewrite Z.eqb_refl. simpl.
    change (filter (fun x => negb (Z.eqb (mint_address x) (mint_address c))) h)
      with (mint_remove h (mint_address c)).
    rewrite remove_absent__user_auth_views by exact Hnot.
    cbn [mint_heap]. cancel.
  - unfold mint_remove; simpl. rewrite E; simpl.
    change (filter (fun x => negb (Z.eqb (mint_address x) (mint_address c))) h)
      with (mint_remove h (mint_address c)).
    cbn [mint_heap].
    sep_apply_r_atomic (IH c Htail Hf). cancel.
    cancel (mint_cell_heap c).
Qed.
Lemma remove_find__user_auth_views : forall h a b,
  a <> b -> mint_find (mint_remove h b) a = mint_find h a.
Proof.
  induction h as [|c h IH]; intros a b Hab; [reflexivity|].
  unfold mint_find, mint_remove in *; simpl.
  destruct (Z.eqb (mint_address c) b) eqn:E; simpl.
  - apply Z.eqb_eq in E. assert (F : Z.eqb (mint_address c) a = false)
      by (apply Z.eqb_neq; congruence).
    rewrite F. apply IH; exact Hab.
  - simpl. destruct (Z.eqb (mint_address c) a); auto.
Qed.
Lemma remove_nodup__user_auth_views : forall h a,
 NoDup (map mint_address h) -> NoDup (map mint_address (mint_remove h a)).
Proof.
  induction h as [|c h IH]; intros a H; [constructor|].
  inversion H as [|? ? Hnot Htail]; subst.
  unfold mint_remove; simpl.
  destruct (Z.eqb (mint_address c) a); simpl; [apply IH; exact Htail|].
  constructor; [|apply IH; exact Htail].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hx Hin]].
  apply filter_In in Hin. apply Hnot. apply in_map_iff. exists x; tauto.
Qed.
Lemma kinds_distinct__user_auth_views : forall h k l a b,
 mint_readable h k a -> mint_readable h l b -> k <> l -> a <> b.
Proof.
 intros h k l a b [v H] [w G] Hkl E. subst b. rewrite H in G. inversion G. contradiction.
Qed.
Lemma auth_restore__user_auth_views : forall h ar pa,
  mint_wellformed h -> mint_readable h 0 ar -> mint_readable h 1 pa ->
  naive_C_Rules.derivable1
    (naive_C_Rules.sepcon (naive_C_Rules.store_uint ar (mint_value h ar))
      (naive_C_Rules.sepcon (naive_C_Rules.store_uchar pa (mint_value h pa))
        (mint_heap (mint_remove (mint_remove h ar) pa)))) (mint_heap h).
Proof.
  Import naive_C_Rules.
  intros h ar pa [Hnd Hk] Har Hpa.
  assert (Hne : pa <> ar) by (eapply kinds_distinct__user_auth_views; eauto; discriminate).
  pose proof (read_cell__user_auth_views h 0 ar Har) as Far.
  pose proof (read_cell__user_auth_views h 1 pa Hpa) as Fpa.
  assert (Fpa' : mint_find (mint_remove h ar) pa = Some (mint_cell 1 pa (Some (mint_value h pa)))).
  { rewrite remove_find__user_auth_views by exact Hne. exact Fpa. }
  pose proof (restore__user_auth_views h (mint_cell 0 ar (Some (mint_value h ar))) Hnd Far) as Rar.
  pose proof (restore__user_auth_views (mint_remove h ar) (mint_cell 1 pa (Some (mint_value h pa)))
    (remove_nodup__user_auth_views h ar Hnd) Fpa') as Rpa.
  cbn [mint_address mint_cell_heap mint_kind mint_initial] in Rar, Rpa.
  sep_apply_l_atomic Rpa. sep_apply_l_atomic Rar. cancel (mint_heap h).
Qed.
Lemma auth_view__user_auth_views : forall h ar pa,
  mint_wellformed h -> mint_auth_reads h ar pa ->
  naive_C_Rules.derivable1 (mint_heap h)
    (naive_C_Rules.orp
      (naive_C_Rules.andp (naive_C_Rules.coq_prop (Z.land (mint_value h ar) 1 = 0))
        (naive_C_Rules.sepcon (naive_C_Rules.store_uint ar (mint_value h ar))
          (mint_heap (mint_remove h ar))))
      (naive_C_Rules.andp (naive_C_Rules.coq_prop (Z.land (mint_value h ar) 1 <> 0))
        (naive_C_Rules.sepcon (naive_C_Rules.store_uint ar (mint_value h ar))
          (naive_C_Rules.sepcon (naive_C_Rules.store_uchar pa (mint_value h pa))
            (mint_heap (mint_remove (mint_remove h ar) pa)))))).
Proof.
  Import naive_C_Rules.
  intros h ar pa [Hnd Hk] [Har Hpa].
  pose proof (read_cell__user_auth_views h 0 ar Har) as Far.
  pose proof (extract__user_auth_views h (mint_cell 0 ar (Some (mint_value h ar))) Hnd Far) as Ear.
  cbn [mint_address mint_cell_heap mint_kind mint_initial] in Ear.
  destruct (Z.eq_dec (Z.land (mint_value h ar) 1) 0) as [Hz|Hz].
  - Left. split_pure_spatial; [exact Ear|]. dump_pre_spatial. exact Hz.
  - specialize (Hpa Hz).
    assert (Hne : pa <> ar) by (eapply kinds_distinct__user_auth_views; eauto; discriminate).
    pose proof (read_cell__user_auth_views h 1 pa Hpa) as Fpa.
    assert (Fpa' : mint_find (mint_remove h ar) pa = Some (mint_cell 1 pa (Some (mint_value h pa)))).
    { rewrite remove_find__user_auth_views by exact Hne. exact Fpa. }
    pose proof (extract__user_auth_views (mint_remove h ar) (mint_cell 1 pa (Some (mint_value h pa)))
      (remove_nodup__user_auth_views h ar Hnd) Fpa') as Epa.
    cbn [mint_address mint_cell_heap mint_kind mint_initial] in Epa.
    Right. split_pure_spatial; [|dump_pre_spatial; exact Hz].
    sep_apply_l_atomic Ear. sep_apply_l_atomic Epa. cancel.
Qed.
Lemma remove_absent__user_auth_results : forall h a,
  ~ In a (map mint_address h) -> mint_remove h a = h.
Proof.
  induction h as [|c t IH]; intros a H; [reflexivity|].
  unfold mint_remove in *; simpl in *.
  assert (E : Z.eqb (mint_address c) a = false) by (apply Z.eqb_neq; intuition).
  rewrite E; simpl. f_equal. apply IH. intuition.
Qed.
Lemma read_factor__user_auth_results : forall h k a,
  mint_wellformed h -> mint_readable h k a ->
  naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value h a)))) (mint_heap (mint_remove h a))) (mint_heap h).
Proof.
  Import naive_C_Rules.
  Local Open Scope sac.
  induction h as [|c t IH]; intros k a [HN HK] [v HF].
  - discriminate HF.
  - inversion HN as [|? ? Hnot Hnt]; subst.
    inversion HK as [|? ? Hkind Hkt]; subst.
    unfold mint_find in HF; simpl in HF.
    destruct (Z.eqb (mint_address c) a) eqn:E.
    + inversion HF; subst c. unfold mint_value, mint_find; simpl.
      rewrite Z.eqb_refl. unfold mint_remove at 1; simpl.
      simpl.
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap (mint_remove t a))) (mint_heap (mint_cell k a (Some v) :: t))).
      rewrite (remove_absent__user_auth_results t a Hnot).
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap t)) (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some v))) (mint_heap t))).
      cancel (mint_heap t). cancel (mint_cell_heap (mint_cell k a (Some v))).
    + assert (RV : mint_value (c :: t) a = mint_value t a).
      { unfold mint_value, mint_find; simpl; rewrite E; reflexivity. }
      rewrite RV. unfold mint_remove at 1; simpl; rewrite E; simpl.
      change (naive_C_Rules.derivable1 (naive_C_Rules.sepcon (mint_cell_heap (mint_cell k a (Some (mint_value t a)))) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap (mint_remove t a)))) (naive_C_Rules.sepcon (mint_cell_heap c) (mint_heap t))).
      sep_apply_r_atomic (IH k a (conj Hnt Hkt) (ex_intro _ v HF)).
      cancel (mint_heap (mint_remove t a)). cancel (mint_cell_heap c). cancel (mint_cell_heap (mint_cell k a (Some (mint_value t a)))).
Qed.
Lemma remove_wf__user_auth_results : forall h a,
 mint_wellformed h -> mint_wellformed (mint_remove h a).
Proof.
 induction h as [|c t IH]; intros a [HN HK]; [split; constructor|].
 inversion HN as [|? ? Hnot Hnt]; subst.
 inversion HK as [|? ? Hk Hkt]; subst.
 specialize (IH a (conj Hnt Hkt)).
 unfold mint_remove; simpl. destruct (Z.eqb (mint_address c) a); simpl; [exact IH|].
 destruct IH as [IN IK]. split; constructor; auto.
 intro Hin. apply Hnot. apply in_map_iff in Hin.
 destruct Hin as [x [Ex Hx]]. apply in_map_iff. exists x. split; auto.
 apply filter_In in Hx. tauto.
Qed.
Lemma remove_find__user_auth_results : forall h a b, a <> b ->
 mint_find (mint_remove h b) a = mint_find h a.
Proof.
 induction h as [|c t IH]; intros a b H; [reflexivity|].
 unfold mint_remove, mint_find in *; simpl.
 destruct (Z.eqb (mint_address c) b) eqn:E; simpl.
 - apply Z.eqb_eq in E. rewrite E. rewrite (proj2 (Z.eqb_neq b a)) by congruence. apply IH; exact H.
 - simpl. destruct (Z.eqb (mint_address c) a); [reflexivity|]. apply IH; exact H.
Qed.
Lemma remove_reads__user_auth_results : forall h k a b, a <> b ->
 mint_readable h k a -> mint_readable (mint_remove h b) k a /\ mint_value (mint_remove h b) a = mint_value h a.
Proof.
 intros h k a b H [v F]. split.
 - exists v. rewrite remove_find__user_auth_results by exact H. exact F.
 - unfold mint_value. rewrite remove_find__user_auth_results by exact H. reflexivity.
Qed.
Lemma kinds_distinct__user_auth_results : forall h k j a b,
 mint_readable h k a -> mint_readable h j b -> k <> j -> a <> b.
Proof. intros h k j a b [v F] [w G] H E. subst b. rewrite F in G. inversion G. contradiction. Qed.
