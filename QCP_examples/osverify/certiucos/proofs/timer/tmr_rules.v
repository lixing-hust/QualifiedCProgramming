Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.


Open Scope code_scope.

Open Scope int_scope.

(*aux RL_TMRL_P*)

Fixpoint AOSTMRList_vallist  (tmrl : list vallist) (n : nat) :=
  match tmrl with 
  | nil => Aemp 
  | vl::tl => AOSTMRNode ($ (Z.of_nat n)) vl** AOSTMRList_vallist tl (S n)
  end.

Fixpoint AOSTMRList_exi' (tmrl : list vallist) (n : nat) (i : nat)  := 
    match tmrl with
      | nil => Aemp
      | y::tl => if  (Nat.eqb n i) then AOSTMRList_vallist tl (S n)
      else (AOSTMRNode ($ (Z.of_nat n)) y) ** (AOSTMRList_exi' tl (S n) i)
    end.

Definition AOSTMRList_exi (tmrl : list vallist) (i: int32) := AOSTMRList_exi' tmrl O (Z.to_nat (Int.unsigned i)).

(*tmr ops*)
Definition intor_val (v : val) (b: val) :=
  match v, b with 
  | (Vint32 v'), (Vint32 b') => (Vint32 (Int.or v' b'))
  | _ , _ => v 
  end.

Definition intand_val (v : val) (b: val) :=
  match v, b with 
  | (Vint32 v'), (Vint32 b') => (Vint32 (Int.and v' b'))
  | _ , _ => v 
  end.

Fixpoint binaryop_nth_val (op: val -> val -> val) (n : nat) (vl : vallist) (v : val) {struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0%nat => (op v' v)::vl'
                  | S n' => v'::(binaryop_nth_val op n' vl' v)
                end
  end. 

Definition tmrlh_op_same (lo: vallist -> vallist) (ho : abstmr.B -> abstmr.B): Prop :=
  forall tmri tmr, 
  (IsGPtmr tmri tmr = true -> IsGPtmr (lo tmri) (ho tmr) = true ) /\ 
  (IsWDtmr tmri tmr = true -> IsWDtmr (lo tmri) (ho tmr) = true ) /\
  (TMRNode_P tmri tmr -> TMRNode_P (lo tmri) (ho tmr)) .

Record tmr_op := mktmrop {
 low_op : vallist -> vallist;
 high_op : abstmr.B -> abstmr.B;
 lh_same: tmrlh_op_same low_op high_op;
}.

Definition lop_stop (tmrl : vallist) := 
  if isGPtmr tmrl then binaryop_nth_val intand_val 8%nat tmrl (Vint32 ($ 4294967292))
  else if isWDtmr tmrl then binaryop_nth_val intand_val 9%nat tmrl (Vint32 ($ 4294950911)) else tmrl.
  
Definition hop_stop (tmr: abstmr.B) :=
   match tmr with 
   (t, t0, t1, om) => (t, tm_idle, t1, om) end.

Ltac my_destruct H :=
  match type of H with 
  | exists _, _ => destruct H as [? H]; my_destruct H 
  | _ /\ _ => let H1:= fresh "H" in 
              destruct H as [H H1];my_destruct H; my_destruct H1
  | _ => idtac 
  end.

Ltac destruct_tmr tmr:=
  let st := fresh "st" in 
  let tk := fresh "tk" in 
  let om := fresh "om" in
 destruct tmr as [[[[? | ?] st] tk] om].

Lemma Pmode_isGPtmr : forall tmri prd m st tick om, 
  TMRNode_Pmode tmri (gp_t prd m, st, tick, om) ->
  isGPtmr tmri = true.
Proof.
  intros.
  unfold TMRNode_Pmode in *.
  unfold isGPtmr.
  destruct m;my_destruct H;do 9 (destruct tmri;tryfalse).
  - cbn in *. inversion H;subst. rewrite H1. mauto.
  - cbn in *. inversion H;subst. rewrite H1. mauto.
Qed.

Lemma Pmode_isWDtmr : forall tmri prd st tick om, 
  TMRNode_Pmode tmri (wd_t prd, st, tick, om) ->
  isGPtmr tmri = false /\ isWDtmr tmri = true.
Proof.
  intros.
  unfold TMRNode_Pmode in *.
  unfold isGPtmr,isWDtmr.
  my_destruct H;do 9 (destruct tmri;tryfalse).
  cbn in *. inversion H;subst. rewrite H0. mauto.
Qed.

Lemma Pmode_isGPorWDtmr : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  isGPtmr tmri = true \/ isGPtmr tmri = false /\ isWDtmr tmri = true.
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  destruct tmr.
  - left. eapply Pmode_isGPtmr;eauto.
  - right. eapply Pmode_isWDtmr;eauto.
Qed.

Lemma lh_modesame_stop : forall tmri tmr, 
  TMRNode_Pmode tmri tmr -> 
  TMRNode_Pmode (lop_stop tmri) (hop_stop tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_stop.
  destruct tmr.
  - lets H0 :  Pmode_isGPtmr H.
    rewrite H0. 
    unfold TMRNode_Pmode in H.
    destruct e.
    + my_destruct H.
      do 9 (destruct tmri;tryfalse).
      cbn in *.
      inversion H;subst. inversion H1;subst. 
      unfold intand_val. 
      do 2 eexists.
      splits;eauto.
      rewrite Int.and_assoc.
      assert ($ 4294967292&ᵢ$ 12 = $ 12) by mauto.
      rewrite H4.
      auto.
    + my_destruct H.
      do 9 (destruct tmri;tryfalse).
      cbn in *.
      inversion H;subst. inversion H1;subst. 
      unfold intand_val. 
      do 2 eexists.
      splits;eauto.
      rewrite Int.and_assoc.
      assert ($ 4294967292&ᵢ$ 12 = $ 12) by mauto.
      rewrite H4.
      auto.
  - lets H0 : Pmode_isWDtmr H.
    destruct H0.
    rewrite H0, H1. 
    unfold TMRNode_Pmode in H.
    my_destruct H.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H;subst.
    eexists. splits;eauto.
Qed.

Lemma lh_cntsame_stop : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pcnt tmri tmr -> 
  TMRNode_Pcnt (lop_stop tmri) (hop_stop tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_stop.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Pcnt in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma lh_prdsame_stop : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pprd tmri tmr -> 
  TMRNode_Pprd (lop_stop tmri) (hop_stop tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_stop.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Pprd in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma lh_statussame_stop : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pstatus tmri tmr -> 
  TMRNode_Pstatus (lop_stop tmri) (hop_stop tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_stop.
  destruct tmr.
  - lets Hmode : Pmode_isGPtmr H.
    rewrite Hmode.
    clear H.
    unfold TMRNode_Pstatus in *.
    destruct st.
    +
    my_destruct H0.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intand_val.
    eexists.
    splits;eauto.
    rewrite Int.and_assoc.
    assert ($ 4294967292&ᵢ$ 3 = $ 0) by mauto.
    rewrite H1.
    apply Int.and_zero.
    +
    my_destruct H0.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intand_val.
    eexists.
    splits;eauto.
    rewrite Int.and_assoc.
    assert ($ 4294967292&ᵢ$ 3 = $ 0) by mauto.
    rewrite H1.
    apply Int.and_zero.
  - lets Hmode : Pmode_isWDtmr H.
    destruct Hmode. clear H.
    rewrite H1. rewrite H2.
    unfold TMRNode_Pstatus in *.
    destruct st.
    +
    my_destruct H0.
    do 10 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intand_val.
    eexists.
    splits;eauto. 
    rewrite Int.and_assoc.
    assert ($ 4294950911&ᵢ$ 16384 = $ 0) by mauto.
    rewrite H3.
    apply Int.and_zero.
    +
    my_destruct H0.
    do 10 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intand_val.
    eexists.
    splits;eauto. 
    rewrite Int.and_assoc.
    assert ($ 4294950911&ᵢ$ 16384 = $ 0) by mauto.
    rewrite H3.
    apply Int.and_zero.
Qed.

Lemma lh_outmodesame_stop : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Poutmode tmri tmr -> 
  TMRNode_Poutmode (lop_stop tmri) (hop_stop tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_stop.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Poutmode in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma isWDtmr_nisGPtmr: forall tmri, isWDtmr tmri = true -> isGPtmr tmri = false.
Proof.
  intros.
  unfold isWDtmr,isGPtmr in *.
  do 9 (destruct tmri;tryfalse).
  cbn [V_OSTGCR nth_val] in *.
  destruct v7;tryfalse.
  apply Int_eq_dec in H.
  rewrite H.
  clear H. mauto.
Qed.

Lemma isGPtmr_nisWDtmr: forall tmri, isGPtmr tmri = true -> isWDtmr tmri = false.
Proof.
  intros.
  unfold isWDtmr,isGPtmr in *.
  do 9 (destruct tmri;tryfalse).
  cbn [V_OSTGCR nth_val] in *.
  destruct v7;tryfalse.
  apply Int_eq_dec in H.
  rewrite H.
  clear H. mauto.
Qed.

Lemma lh_gpsame_stop: forall tmri tmr,
  IsGPtmr tmri tmr = true -> IsGPtmr (lop_stop tmri) (hop_stop tmr) = true.
Proof.
  intros.
  unfold IsGPtmr in *.
  apply andb_true_iff in H as [? ?].
  apply andb_true_iff.
  split.
  - unfold lop_stop. rewrite H.
  do 9 (destruct tmri;tryfalse).
  unfold isGPtmr in *.
  cbn [V_OSTGCR nth_val binaryop_nth_val ] in *.
  destruct v7;tryfalse.
  cbn [intand_val].
  rewrite Int.and_assoc.
  assert (($ 4294967292&ᵢ$ 12) = $ 12) by mauto.
  rewrite H1.
  auto.
  - unfold hop_stop, isgptmr in *. 
    destruct_tmr tmr;auto.
Qed.

Lemma lh_wdsame_stop: forall tmri tmr,
  IsWDtmr tmri tmr = true -> IsWDtmr (lop_stop tmri) (hop_stop tmr) = true.
Proof.
  intros.
  unfold IsWDtmr in *.
  apply andb_true_iff in H as [? ?].
  apply andb_true_iff.
  split.
  - unfold lop_stop.
  apply isWDtmr_nisGPtmr in H as ?.
  rewrite H1,H.
  do 9 (destruct tmri;tryfalse).
  unfold isWDtmr in *.
  cbn [V_OSTGCR nth_val binaryop_nth_val ] in *.
  destruct v7;tryfalse.
  auto.
  - unfold hop_stop, iswdtmr in *. 
    destruct_tmr tmr;auto.
Qed.

Lemma lh_same_stop: tmrlh_op_same lop_stop hop_stop.
Proof. 
  unfold tmrlh_op_same. intros.
  splits.
  - apply lh_gpsame_stop.
  - apply lh_wdsame_stop.
  - intros.
  unfold TMRNode_P in *. my_destruct H.
  unfold TMRNode_P in *.  
  my_destruct H0.
  splits.
  apply lh_modesame_stop;auto.
  apply lh_cntsame_stop;auto.
  apply lh_prdsame_stop;auto.
  apply lh_statussame_stop;auto.
  apply lh_outmodesame_stop;auto.
Qed.

Definition stop_tmrop : tmr_op := mktmrop lop_stop hop_stop lh_same_stop. 

Definition lop_start (tmrl : vallist) := 
  if isGPtmr tmrl then binaryop_nth_val intor_val 8%nat tmrl (Vint32 ($ 3))
  else if isWDtmr tmrl then binaryop_nth_val intor_val 9%nat tmrl (Vint32 ($ 16384)) else tmrl.
  
Definition hop_start (tmr: abstmr.B) :=
   match tmr with 
   (t, t0, t1, om) => (t, tm_start, t1, om) end.

Lemma lh_modesame_start : forall tmri tmr, 
  TMRNode_Pmode tmri tmr -> 
  TMRNode_Pmode (lop_start tmri) (hop_start tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_start.
  destruct tmr.
  - lets H0 :  Pmode_isGPtmr H.
    rewrite H0. 
    unfold TMRNode_Pmode in H.
    destruct e.
    + my_destruct H.
      do 9 (destruct tmri;tryfalse).
      cbn in *.
      inversion H;subst. inversion H1;subst. 
      unfold intor_val. 
      do 2 eexists.
      splits;eauto.
      rewrite Int.and_or_distrib_l.
      rewrite H2.
      assert (($ 3&ᵢ$ 12) = $ 0) by mauto.
      rewrite H4.
      mauto.
    + my_destruct H.
      do 9 (destruct tmri;tryfalse).
      cbn in *.
      inversion H;subst. inversion H1;subst. 
      unfold intor_val. 
      do 2 eexists.
      splits;eauto.
      rewrite Int.and_or_distrib_l.
      rewrite H2.
      assert (($ 3&ᵢ$ 12) = $ 0) by mauto.
      rewrite H4.
      mauto.
  - lets H0 : Pmode_isWDtmr H.
    destruct H0.
    rewrite H0, H1. 
    unfold TMRNode_Pmode in H.
    my_destruct H.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H;subst.
    eexists. splits;eauto.
Qed.

Lemma lh_cntsame_start : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pcnt tmri tmr -> 
  TMRNode_Pcnt (lop_start tmri) (hop_start tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_start.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Pcnt in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma lh_prdsame_start : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pprd tmri tmr -> 
  TMRNode_Pprd (lop_start tmri) (hop_start tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_start.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Pprd in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma lh_statussame_start : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Pstatus tmri tmr -> 
  TMRNode_Pstatus (lop_start tmri) (hop_start tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_start.
  destruct tmr.
  - lets Hmode : Pmode_isGPtmr H.
    rewrite Hmode.
    clear H.
    unfold TMRNode_Pstatus in *.
    destruct st.
    +
    my_destruct H0.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intor_val.
    eexists.
    splits;eauto.
    rewrite Int.and_or_distrib_l.
    rewrite H.
    assert (($ 3&ᵢ$ 3) = $ 3) by mauto.
    mauto.
    +
    my_destruct H0.
    do 9 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intor_val.
    eexists.
    splits;eauto.
    rewrite Int.and_or_distrib_l.
    rewrite H.
    assert (($ 3&ᵢ$ 3) = $ 3) by mauto.
    mauto.
  - lets Hmode : Pmode_isWDtmr H.
    destruct Hmode. clear H.
    rewrite H1. rewrite H2.
    unfold TMRNode_Pstatus in *.
    destruct st.
    +
    my_destruct H0.
    do 10 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intor_val.
    eexists.
    splits;eauto. 
    rewrite Int.and_or_distrib_l.
    rewrite H.
    mauto.
    +
    my_destruct H0.
    do 10 (destruct tmri;tryfalse).
    cbn in *.
    inversion H0;subst.
    unfold intor_val.
    eexists.
    splits;eauto. 
    rewrite Int.and_or_distrib_l.
    rewrite H.
    mauto.
Qed.

Lemma lh_outmodesame_start : forall tmri tmr, 
  TMRNode_Pmode tmri tmr ->
  TMRNode_Poutmode tmri tmr -> 
  TMRNode_Poutmode (lop_start tmri) (hop_start tmr).
Proof.
  intros.
  destruct tmr as (((tmr, st), tick), om).
  cbn. unfold lop_start.
  lets Hmode : Pmode_isGPorWDtmr H.
  unfold TMRNode_Pmode in H.
  do 9 (destruct tmri;[
  destruct tmr;[destruct e;my_destruct H |my_destruct H ];tryfalse | ]).
  unfold TMRNode_Poutmode in *.
  let h1 := fresh in let h2 := fresh in
  destruct Hmode as [h1 | [h1 h2]];[rewrite h1| rewrite h1,h2];cbn in *;auto.
Qed.

Lemma lh_gpsame_start: forall tmri tmr,
  IsGPtmr tmri tmr = true -> IsGPtmr (lop_start tmri) (hop_start tmr) = true.
Proof.
  intros.
  unfold IsGPtmr in *.
  apply andb_true_iff in H as [? ?].
  apply andb_true_iff.
  split.
  - unfold lop_start. rewrite H.
  do 9 (destruct tmri;tryfalse).
  unfold isGPtmr in *.
  cbn [V_OSTGCR nth_val binaryop_nth_val ] in *.
  destruct v7;tryfalse.
  cbn [intor_val].
  apply Int_eq_dec in H.
  apply Int_eq_dec.
  apply or_and_combine_zero;auto.
  - unfold hop_start, isgptmr in *. 
    destruct_tmr tmr;auto.
Qed.

Lemma lh_wdsame_start: forall tmri tmr,
  IsWDtmr tmri tmr = true -> IsWDtmr (lop_start tmri) (hop_start tmr) = true.
Proof.
  intros.
  unfold IsWDtmr in *.
  apply andb_true_iff in H as [? ?].
  apply andb_true_iff.
  split.
  - unfold lop_start.
  apply isWDtmr_nisGPtmr in H as ?.
  rewrite H1,H.
  do 9 (destruct tmri;tryfalse).
  unfold isWDtmr in *.
  cbn [V_OSTGCR nth_val binaryop_nth_val ] in *.
  destruct v7;tryfalse.
  auto.
  - unfold hop_stop, iswdtmr in *. 
    destruct_tmr tmr;auto.
Qed.

Lemma lh_same_start: tmrlh_op_same lop_start hop_start.
Proof. 
  unfold tmrlh_op_same. intros.
  splits.
  - apply lh_gpsame_start.
  - apply lh_wdsame_start. 
  - intros. 
  unfold TMRNode_P in *. my_destruct H.
  unfold TMRNode_P in *.  
  my_destruct H0.
  splits.
  apply lh_modesame_start;auto.
  apply lh_cntsame_start;auto.
  apply lh_prdsame_start;auto.
  apply lh_statussame_start;auto.
  apply lh_outmodesame_start;auto.
Qed.

Definition start_tmrop : tmr_op := mktmrop lop_start hop_start lh_same_start. 

Lemma Timer_TGCR_off_eq : 
  forall i i0, 
  Int.ltu i ($ 16) = true ->
  (i0 +ᵢ  Int.mul ($ 9) ($ 4)) +ᵢ  Int.mul (i<<ᵢ$ 14) ($ 4) = 
  (i0 +ᵢ  $ 36) +ᵢ  Int.mul i ($ 65536).
Proof.
  intros.
  assert (Int.mul ($ 9) ($ 4) = $ 36 ) by pauto.
  rewrite H0.
  assert ( Int.mul i ($ 16384) = i<<ᵢ$ 14 ).
  { eapply Int.mul_pow2;pauto.  } 
  rewrite <- H1.
  rewrite Int.mul_assoc.
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  rewrite H2.
  reflexivity.
Qed.

Lemma Timer_CNTLO_off_eq : 
  forall i i0, 
  Int.ltu i ($ 16) = true ->
  (i0 +ᵢ  Int.mul ($ 4) ($ 4)) +ᵢ  Int.mul (Int.mul i ($ 16384)) ($ 4) = 
  (i0 +ᵢ  $ 16) +ᵢ  Int.mul i ($ 65536).
Proof.
  intros.
  assert (Int.mul ($ 4) ($ 4) = $ 16 ) by pauto.
  rewrite H0.
  rewrite Int.mul_assoc.
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  rewrite H1.
  reflexivity.
Qed.

Lemma Timer_CNTHI_off_eq : 
  forall i i0, 
  Int.ltu i ($ 16) = true ->
  (i0 +ᵢ  Int.mul ($ 5) ($ 4)) +ᵢ  Int.mul (Int.mul i ($ 16384)) ($ 4) = 
  (i0 +ᵢ  $ 20) +ᵢ  Int.mul i ($ 65536).
Proof.
  intros.
  assert (Int.mul ($ 5) ($ 4) = $ 20) by pauto.
  rewrite H0.
  rewrite Int.mul_assoc.
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  rewrite H1.
  reflexivity.
Qed.

Lemma tcblist_prio_lt64:
     forall v'33 v'32 v'28 x7 x6 i6 i5 i4 i3 i2 i1 i0 v'12 v'13 v'31,
     TCBList_P (Vptr (v'33, Int.zero))
        ((v'32
          :: v'28
             :: x7
                :: x6
                   :: Vint32 i6
                      :: Vint32 i5
                         :: Vint32 i4
                            :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) :: v'12) v'13 v'31 ->
    (Int.unsigned i4 < Z.of_nat 64)%Z.
Proof. 
  intros.
  unfold TCBList_P in H; fold TCBList_P in H.
  destruct H. do 3 destruct H.   
  destruct x2. destruct p. destruct p.
  destruct H as  [_ [_ [_ [[_ [_ [ Hi4 _ ]]] _ ] ] ] ].
  unfold RL_TCBblk_P in Hi4.
  destruct Hi4. do 5 destruct H. destruct H as [Hi4 [_ [_ [_ [_ [_ [Hi4' _ ]]]]]]].
  cbn in Hi4. inversion Hi4. pauto.
Qed. 


Lemma tcblist_prio_lt64' : 
  forall vl tid prio vl1 vl2 x, 
  V_OSTCBPrio vl = Some (Vint32 prio) ->
  TCBList_P (Vptr tid) (vl :: vl1) vl2 x ->
  (Int.unsigned prio < Z.of_nat 64)%Z.
Proof.
  intros.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  do 4 destruct H0.
  destruct H0. destruct H1. destruct H2. destruct H3.
  unfold TCBNode_P, RL_TCBblk_P in H3.
  destruct x3. destruct p. destruct p.
  destruct H3 as [_ [Hp [H3 _ ]]].
  do 6 destruct H3.
  destruct H3 as [Hi4 [_ [_ [_ [_ [_ [Hi4' _ ]]]]]]].
  rewrite H in Hi4.
  inversion Hi4. tauto.
Qed.

Lemma get_get_set :
 forall [A B T : Type] [MC : PermMap A B T] (m : T) (a a' : A) (b b': B),
   get m a = Some b ->
   exists x, get (set m a' b') a = Some x . 
Proof.
  intros.
  rewrite set_sem.
  destruct (dec a' a).
  eexists;eauto.
  eexists;eauto.
Qed.
Lemma get_get_set_andp :
 forall [A B T : Type] [MC : PermMap A B T](P: B -> Prop) (m : T) (a a' : A) (b b': B),
   P b -> P b' ->
   get m a = Some b ->
   exists x, get (set m a' b') a = Some x /\ P x. 
Proof.
  intros.
  rewrite set_sem.
  destruct (dec a' a).
  eexists;eauto.
  eexists;eauto.
Qed.

Lemma join_sig_join_sig_eq :
 forall [A B T : Type] [MC : PermMap A B T] (m m1 m2: T) (a : A) (b b': B),
  usePerm = false ->
  join (sig a b) m1 m ->
  join (sig a b') m2 m ->  
  b = b' /\ m1 = m2.
Proof.
  intros.
  assert (get m a = Some b).
  { eapply join_sig_get;eauto. }
  assert (get m a = Some b').
  { eapply join_sig_get;eauto. }
  assert (b = b').
  { eapply map_get_unique;eauto. }
  rewrite H4 in *. 
  assert (m1 = m2).
  { eapply join_unique_r; eauto. }
  tauto.
Qed.

Lemma join_sig_nindom :
 forall [A B T : Type] [MC : PermMap A B T] (m m1: T) (a : A) (b: B),
  usePerm = false ->
  join (sig a b) m1 m -> 
  ~ indom m1 a.
Proof.
  intros.
  assert (disjoint (sig a b) m1).
  { eapply map_tactics.join_disj;eauto. }
  eapply disj_indom with (a:= a) in H1;eauto.
  destruct H1.
  apply H1.
  eapply get_indom.
  exists b.
  apply get_a_sig_a.
Qed.

Theorem good_frm_AOSTMRList_vallist : 
forall tmrl n, GoodFrm (AOSTMRList_vallist tmrl n).
Proof.
  induction tmrl;intros.
  - cbn;auto.
  - cbn [AOSTMRList_vallist]. 
    eapply good_frm_star.
    go.
    apply IHtmrl.
Qed.

Hint Resolve good_frm_AOSTMRList_vallist : good_frm_lemmas.

Theorem good_frm_AOSTMRList_exi':
 forall tmrl n m, GoodFrm (AOSTMRList_exi' tmrl n m).
 Proof.
  induction tmrl;intros.
  - cbn;auto.
  - unfold AOSTMRList_exi';fold AOSTMRList_exi'.
    destruct  (n =? m)%nat eqn:?.
    go.
    eapply good_frm_star.
    go.
    apply IHtmrl.
Qed.

Hint Resolve good_frm_AOSTMRList_exi' : good_frm_lemmas.

Theorem good_frm_AOSTMRList_exi:
 forall tmrl n, GoodFrm (AOSTMRList_exi tmrl n).
 Proof.
  unfold AOSTMRList_exi. intros.
  go.
Qed.

Hint Resolve good_frm_AOSTMRList_exi : good_frm_lemmas.

Theorem  can_change_aop_AOSTMRList_vallist : 
forall tmrl n, can_change_aop (AOSTMRList_vallist tmrl n).
Proof.
  induction tmrl;intros.
  - cbn;auto.
  - cbn [AOSTMRList_vallist]. 
    eapply can_change_aop_star.
    can_change_aop_solver.
    apply IHtmrl.
Qed.

Hint Resolve can_change_aop_AOSTMRList_vallist : can_change_aop.

Theorem can_change_aop_AOSTMRList_exi':
 forall tmrl n m, can_change_aop (AOSTMRList_exi' tmrl n m).
 Proof.
  induction tmrl;intros.
  - cbn;auto.
  - unfold AOSTMRList_exi';fold AOSTMRList_exi'.
    destruct  (n =? m)%nat eqn:?.
    can_change_aop_solver.
    eapply can_change_aop_star.
    can_change_aop_solver.
    apply IHtmrl.
Qed.

Hint Resolve can_change_aop_AOSTMRList_exi' : can_change_aop.

Theorem can_change_aop_AOSTMRList_exi : 
  forall tmrl i, can_change_aop (AOSTMRList_exi tmrl i).
Proof.
  unfold AOSTMRList_exi;intros.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSTMRList_exi : can_change_aop.

Require Import join_lib_aux.
Require Import Lia.


Lemma TMRList_P_user_update_tmr :
  forall tmrl usedl tmrls tmri n m tmr (lh : tmr_op) ,
  nth_error tmrl m = Some tmri ->
  get tmrls (Z.of_nat (n+m+8)) = Some tmr ->
  (m < length tmrl)%nat ->
  TMRList_P_user n tmrl usedl tmrls ->
  TMRList_P_user n (update_nth_vallist m tmrl (lh.(low_op) tmri)) usedl
  (set tmrls (Z.of_nat (n+m+8)) (lh.(high_op) tmr)).
Proof.
  induction tmrl;intros.
  - cbn [TMRList_P_user update_nth_vallist ] in *. 
    destruct usedl;tryfalse.
    rewrite H2 in *.
    inversion H0. 
  - cbn [TMRList_P_user update_nth_vallist ] in *.
    destruct usedl;tryfalse.
    destruct m.
    +
      cbn [nth_error ] in H. inversion H;subst.
      destruct v;tryfalse.
      unfold TMRList_P_user;fold TMRList_P_user.
      rewrite Nat.add_0_r in H0.
      destruct H2 as [ H2 | H2]. 
      2: { false.
           my_destruct H2. 
           apply H4.
           eapply get_indom.
           eexists. eauto. }
      my_destruct H2.
      assert (get tmrls (Z.of_nat (n+8)) = Some x).
      { eapply join_sig_get ;eauto. }
      pose proof (map_get_unique H7 H0).
      subst x.
      left.
      pose proof lh_same lh tmri tmr as [? [_ ?]].
      specialize (H8 H3).
      specialize (H9 H4).
      split;auto.
      exists (high_op lh tmr). eexists.
      splits;eauto.
      rewrite Nat.add_0_r.
      eapply join_sig_set;eauto.
    +  cbn [nth_error ] in H.
       destruct v;tryfalse.
       unfold TMRList_P_user;fold TMRList_P_user.
       assert (n + S m  + 8 = S n + m + 8 )%nat by lia.
       rewrite H3 in *; clear H3.
       simpl in H1. 
       apply lt_S_n in H1.
       destruct H2 as [ H2 | H2].
       * my_destruct H2.
         left.
         splits;eauto.
         do 2 eexists.
         assert (get x0 (Z.of_nat (S n + m + 8)) = Some tmr).
         { eapply join_sig_get_neq;eauto. lia. }
         splits;eauto.
         eapply join_set_r;eauto.
         eapply get_indom.
         eexists. eauto.
       * my_destruct H2.
         right.
         splits;eauto.
         apply nindom_get_rev.
         erewrite neq_set_get;[ | lia].
         apply nindom_get;auto.
Qed.

Lemma RLH_TMRList_P_user_update_tmr :
  forall tmrl usedl tmrls tmri z tmr (lh : tmr_op) ,
  8 <= z < 16 ->
  length tmrl = 8%nat ->
  nth_error tmrl (Z.to_nat z - 8) = Some tmri ->
  get tmrls z = Some tmr ->
  RLH_TMRList_P_user tmrl usedl tmrls ->
  RLH_TMRList_P_user (update_nth_vallist (Z.to_nat z - 8)%nat tmrl (lh.(low_op) tmri)) usedl
  (set tmrls z (lh.(high_op) tmr)).
Proof.
  unfold RLH_TMRList_P_user; intros.
  assert (z = (Z.of_nat (O+ (Z.to_nat z - 8) +8))) by lia.
  rewrite H4 in H2.
  rewrite H4 at 2. 
  eapply TMRList_P_user_update_tmr;eauto.
  lia.
Qed.

Lemma RLH_TMRused_is1 :
  forall n tmrl tmri usedl tmrls,
  nth_error tmrl n = Some tmri ->
  TMR_used n usedl ->
  RLH_TMRList_P_user tmrl usedl tmrls ->
  exists abstmr, IsGPtmr tmri abstmr = true /\ get tmrls (Z.of_nat n + 8) = Some abstmr /\ 
  TMRNode_P tmri abstmr. 
Proof.
 intros.
 unfold RLH_TMRList_P_user in H1.
 assert (n = n + 0)%nat by lia.
 rewrite H2.
 clear H2.
 remember 0%nat as m.
 clear Heqm.
 revert m tmrl tmri usedl tmrls H H0 H1.
 induction n;intros.
 - destruct tmrl;tryfalse.
   destruct usedl;tryfalse.
   cbn [nth_error TMRList_P_user] in *.
   inversion H;subst.
   destruct v0;tryfalse.
   destruct H1 as [[? [? [? [? [? [?]]]]]] | [? _ ]].
  + eexists. splits;eauto.
    assert ((Z.of_nat (0 + m) + 8) = (Z.of_nat (m + 8)))%Z by lia.
    rewrite H6.
    eapply join_sig_get;eauto.
  + unfold TMR_used in H0.
    simpl in H0.
    inversion H0.
    rewrite H3 in H1.
    tryfalse.
 - destruct tmrl;tryfalse.
   destruct usedl;tryfalse.
   unfold TMR_used in *.
   cbn [nth_error TMRList_P_user] in *.
   destruct v0;tryfalse.
   destruct H1 as [H1 | H1].
  + my_destruct H1.
    assert (S n + m = n + S m)%nat by lia.
    rewrite H6.
    specialize (IHn (S m) tmrl tmri usedl x0 H H0 H5).
    my_destruct IHn.
    eexists;splits;eauto.
    eapply join_get_r;eauto.
  + my_destruct H1.
    assert (S n + m = n + S m)%nat by lia.
    rewrite H5.
    eapply IHn;eauto.
Qed.

Lemma RLH_TMRused_is0 :
  forall n tmrl usedl tmrls,
  length tmrl = length usedl ->
  nth_error usedl n = Some (Vint32 ($ 0)) ->
  RLH_TMRList_P_user tmrl usedl tmrls ->
  ~ indom tmrls (Z.of_nat n + 8). 
Proof.
 intros.
 unfold RLH_TMRList_P_user in H1.
 assert (n = n + 0)%nat by lia.
 rewrite H2.
 clear H2.
 remember 0%nat as m.
 clear Heqm.
 revert m tmrl usedl tmrls H H0 H1.
 induction n;intros.
 - destruct usedl;tryfalse.
   destruct tmrl;tryfalse.
   cbn [nth_error TMRList_P_user] in *.
   simpl in H.
   destruct v;tryfalse.
   destruct H1 as [[? [? [? [? [? [?]]]]]] | [? [? ?] ]].
   + inversion H0. subst. tryfalse.
   + assert ((Z.of_nat (0 + m) + 8) = (Z.of_nat (m + 8)))%Z by lia.
     rewrite H4. 
     my_destruct H3. auto.  
 - destruct usedl;tryfalse.
   destruct tmrl;tryfalse.
   cbn [nth_error TMRList_P_user] in *.
   simpl in H.
   apply eq_add_S in H.
   destruct v;tryfalse.
   destruct H1 as [[? [? [? [? [? [?]]]]]] | [? [? ?] ]].
  + assert (S n + m = n + S m)%nat by lia.
    rewrite H6.
    specialize (IHn (S m) tmrl  usedl x0 H H0 H5).
    unfold not;intro.
    apply IHn.
    unfold indom in *.
    destruct H7.
    eexists.
    eapply join_sig_get_neq;eauto. lia.
  + assert (S n + m = n + S m)%nat by lia.
    rewrite H4.
    my_destruct H3.
    eapply IHn;eauto.
Qed.

Lemma tmrid_destruct :
forall i ,
    Int.lt ($ -1) i = true -> 
    Int.lt i ($ 16) = true ->
    (i = $ 0 \/ i = $ 1 \/ i = $ 2 \/ i = $ 3 \/ i = $ 4 \/ i = $5 \/ i = $ 6 \/ i = $ 7 \/ 
    i = $ 8 \/ i = $ 9 \/ i = $ 10 \/ i = $ 11 \/ i = $12 \/
    i = $13 \/ i = $ 14 \/ i =$ 15).
Proof.
  intros.
  simpl_intltbool.
  remember (Int.signed i) as iz.
  assert ( iz = 0 \/ iz = 1 \/ iz = 2 \/ iz = 3 \/ iz = 4 \/ iz = 5 \/ iz = 6 \/ iz = 7 \/
  iz = 8 \/ iz = 9 \/ iz = 10 \/ iz = 11 \/ iz = 12 \/
  iz = 13 \/ iz = 14 \/ iz = 15)%Z. 
  { clear - H H0. 
  lia. }
  rewrite Heqiz in H1.
  clear - H1.
  destruct H1 as [H | [H | [H | [H | [H | [H | [ H| [H | [H | [H | [H | [H | [ H| [H | [ H| H]]]]]]]]]]]]]]].
  all : try (pose proof Int.repr_signed i as H0; rewrite H in H0; symmetry in H0; tauto).
Qed.

Lemma Int_lt_mone : forall i , Int.unsigned i <= Int.max_signed -> Int.lt ($ -1) i = true.
Proof.
  intros.
  unfold Int.lt.
  apply Int.signed_positive in H.
  destruct (zlt (Int.signed ($ -1)) (Int.signed i)) ;auto.
  rewrite Int.signed_repr in g.
  lia.
  unfold Int.min_signed, Int.max_signed,Int.half_modulus.
  mauto.
Qed.

Lemma tmri_ltmone: forall i, Int.ltu i ($ 16) = true -> Int.lt ($ -1) i = true.
Proof.
  intros.
  apply Int_lt_mone.
  simpl_intltbool.
  unfold Int.max_signed,Int.half_modulus.
  mauto.
Qed.

Lemma tmri_lt16 : forall i,
Int.ltu i ($ 16) = true ->  Int.lt i ($ 16) = true.
Proof.
  intros.
  simpl_intltbool.
  unfold Int.lt.
  destruct (zlt (Int.signed i) (Int.signed ($ 16)) );auto.
  rewrite Int.signed_repr in g.
  rewrite Int.signed_eq_unsigned in g.
  lia.
  {  unfold Int.max_signed,Int.half_modulus.
  mauto. }
  { unfold Int.min_signed, Int.max_signed,Int.half_modulus.
  mauto. }
Qed.

 
Lemma update_nth_vallist_nth_error:
  forall n vl v,
   nth_error vl n = Some v ->
   update_nth_vallist n vl v = vl.
Proof.
  induction n;intros.
  - destruct vl;cbn [nth_error] in *. 
    discriminate.
    inversion H;subst.
    cbn [update_nth_vallist].
    auto.
  - destruct vl;cbn [nth_error] in *.
    discriminate.
    cbn [update_nth_vallist].
    specialize (IHn vl v H).
    rewrite IHn.
    auto.
Qed.

Lemma length_update_nth_vallist: forall vl n v, length (update_nth_vallist n vl v) = length vl.
Proof.
  induction vl;intros.
  - simpl. auto.
  - destruct n;simpl;auto.
Qed.

Lemma update_nth_vallist_app1: forall n vl1 vl2 v,
 (n < length vl1 )%nat ->
 update_nth_vallist n (vl1 ++ vl2) v = 
 (update_nth_vallist n vl1 v) ++ vl2.
Proof.
  induction n;intros.
  - destruct vl1; simpl in *;[ false;lia | auto].
  - destruct vl1.
    + simpl in H. false;lia.
    + simpl in *.
      apply le_S_n in H.
      specialize (IHn vl1 vl2 v H).
      rewrite IHn.
      auto.
Qed.

Lemma update_nth_vallist_app2: forall n vl1 vl2 v,
 (length vl1 <= n)%nat ->
 update_nth_vallist n (vl1 ++ vl2) v = vl1 ++ (update_nth_vallist (n - length vl1) vl2 v).
Proof.
  induction n;intros.
  - destruct vl1; simpl in *;[ auto | false;lia].
  - destruct vl1.
    + simpl in *.
      auto.
    + simpl in *.
      apply le_S_n in H.
      specialize (IHn vl1 vl2 v H).
      rewrite IHn.
      auto.
Qed.


Lemma tmr_absinfer_TMRnotERROR_abort :
    forall P sch aop tm tid,  
      can_change_aop P ->
              absinfer sch (<|| ASSERT TMRnotERROR;; aop ||> **
              HTime tm **
              HCurTCB tid **
              HTMRList None ** P)
      (<|| ABORT ||>  ** 
      HTime tm **
      HCurTCB tid **
      HTMRList None **  P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= HTime tm ** HCurTCB tid ** HTMRList None ** P).
  can_change_aop_solver.
  can_change_aop_solver.

  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | sep auto | ].
  intros.
  destruct s as [[[[[[]]]]]]. 
  unfold not,TMRnotERROR;simpl.
  intros.
  destruct H1.
  sep remember (3::nil)%nat in H0.
  simpl_sat H0.
  simpljoin1.
  assert (get o ostmrid = Some (ostmr None)).
  {  eapply join_sig_get;eauto. }
  rewrite H1 in H0.
  discriminate.
   
  eapply absinfer_seq_abt.
  1,2: can_change_aop_solver.
  sep auto.
Qed.

Lemma tmr_absinfer_TMRnotERROR_cont :
    forall P sch aop tm tmrls tid,  
      can_change_aop P ->
              absinfer sch (<|| ASSERT TMRnotERROR;; aop ||> **
              HTime tm **
              HCurTCB tid **
              HTMRList (Some tmrls) ** P)
      (<|| aop ||>  ** 
      HTime tm **
      HCurTCB tid **
      HTMRList (Some tmrls) **  P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= HTime tm ** HCurTCB tid ** HTMRList (Some tmrls)** P).
  can_change_aop_solver.
  can_change_aop_solver.

  eapply absinfer_assert_cont ;[can_change_aop_solver | can_change_aop_solver | sep auto | ].
  intros.
  destruct s as [[[[[[]]]]]]. 
  unfold TMRnotERROR;simpl.
  sep remember (3::nil)%nat in H0.
  simpl_sat H0.
  simpljoin1.
  eexists.
  eapply join_sig_get;eauto. 
   
  eapply absinfer_seq_end.
  1,2: can_change_aop_solver.
  sep auto.
Qed.

Lemma tmr_absinfer_valvptr_abt:
    forall P sch s, can_change_aop P ->
              absinfer sch (<|| ASSERT (tmr_valvptr Vnull) ;;  s ||> ** P) (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= P).
  1,2: can_change_aop_solver.

  eapply absinfer_assert_abt; try (eauto || can_change_aop_solver).
  apply absinfer_seq_abt.
  1,2: can_change_aop_solver.
  sep auto.
Qed.

Lemma tmr_absinfer_valvptr_cont:
    forall P sch s x, can_change_aop P ->
              absinfer sch (<|| ASSERT (tmr_valvptr (Vptr x)) ;;  s ||> ** P) (<|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (q:= P).
  1,2: can_change_aop_solver.

  eapply absinfer_assert_cont; try (eauto || can_change_aop_solver).
  intros.
  unfold tmr_valvptr; auto.
  apply absinfer_seq_end.
  1,2: can_change_aop_solver.
  sep auto.
Qed.