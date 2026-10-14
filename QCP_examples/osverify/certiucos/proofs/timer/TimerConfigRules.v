Require Import ucos_include.
Require Import Lia.

Require Import join_lib_aux.
Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.

Open Scope int_scope.

Lemma OS_timerConfigProofPart0: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i: int32)
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  LV timerx @ OSTimerRegs ∗ |-> v' **
  GV __timerregs @ (Int32u) ∗ |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 tmrid_i **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ =ₑ〈 OSTimerRegs ∗ 〉 (__timerregs ′ +ₑ (os_code_defs.timerid ′ ≪ ′ 14))
{{ <|| aop ||>  **
  LV timerx @ OSTimerRegs ∗ |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  GV __timerregs @ (Int32u) ∗ |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 tmrid_i **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  destruct tmrRegsAddr eqn: Htmraddr.
  eapply forward_rule2.
  hoare forward.

  intros.
  assert (Int.ltu ($ 14) Int.iwordsize = true) by pauto.
  rewrite H2 in *.
  cbn [val_inj] in *.
  assert ( Int.mul tmrid_i ($ 16384) = tmrid_i<<ᵢ$ 14 ).
  { eapply Int.mul_pow2;pauto.  } 
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  rewrite <- H3 in H1.
  rewrite Int.mul_assoc in H1.
  rewrite H4 in H1.
  sep auto.
Qed.

Definition pre28bits' (v : val)  : int32 :=
   match v with
   | Vint32 v' => pre28bits v'
   | _ => Int.mone
   end.

Lemma AOSTMRNode_Astruct_frm : 
 forall i tmri p ,
 AOSTMRNode i tmri ** p <==> 
 [| length tmri = 10%nat|] **
 [|exists wdtcr, (val_inj (nth_error tmri 9%nat)) = Vint32 wdtcr|] **
 [|  pre28bits' (val_inj (nth_error tmri 8%nat)) = Int.zero |] **
 Astruct (get_off_addr tmrRegsAddr (Int.mul i ($ 65536))) OSTimerRegs (firstn 9%nat tmri) **
 [| struct_type_vallist_match OSTimerRegs (firstn 9%nat tmri) |] **
 PV timer_WDTCR i @ Int32u |-> (val_inj (nth_error tmri 9%nat))  ** p.
Proof.
  intros.
  unfold AOSTMRNode.
   unfold Astruct,OSTimerRegs.
  unfold timer_RSVD0,timer_EMUMGT_CLKSPD,timer_RSVD1,timer_CNTLO,
  timer_CNTHI,timer_PRDLO, timer_PRDHI, timer_TCR, timer_TGCR.
  destruct tmrRegsAddr eqn :?.
  unfold get_off_addr .
  cbn [ typelen fst snd] .

  assert ( (i0 +ᵢ  $ 4) +ᵢ  Int.mul i ($ 65536) = (i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4  ).
  { do 2 rewrite Int.add_assoc.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 16) +ᵢ  Int.mul i ($ 65536) =  (((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat (4 * 2)).
  { do 4 rewrite Int.add_assoc.
    assert (($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat (4 * 2))) = $ 16) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 20) +ᵢ  Int.mul i ($ 65536) =  ((((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ $ Z.of_nat (4 * 2)) +ᵢ  $ Z.of_nat 4).
  { do 5 rewrite Int.add_assoc.
    assert (($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat (4 * 2) +ᵢ  $ Z.of_nat 4))) = $ 20) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 24) +ᵢ  Int.mul i ($ 65536) =  (((((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat (4 * 2)) +ᵢ  $ Z.of_nat 4) +ᵢ   $ Z.of_nat 4).
  { do 6 rewrite Int.add_assoc.
    assert (($ Z.of_nat 4 +ᵢ
  ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat (4 * 2) +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4)))) = $ 24) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 28) +ᵢ  Int.mul i ($ 65536) =  ((((((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat (4 * 2)) +ᵢ  $ Z.of_nat 4) +ᵢ   $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4).
  { do 7 rewrite Int.add_assoc.
    assert ( ($ Z.of_nat 4 +ᵢ
  ($ Z.of_nat 4 +ᵢ
   ($ Z.of_nat (4 * 2) +ᵢ  ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4))))) = $ 28) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 32) +ᵢ  Int.mul i ($ 65536) =   (((((((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4)
          +ᵢ  $ Z.of_nat (4 * 2)) +ᵢ  $ Z.of_nat 4) +ᵢ  
        $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4).
  { do 8 rewrite Int.add_assoc.
    assert ( ($ Z.of_nat 4 +ᵢ
  ($ Z.of_nat 4 +ᵢ
   ($ Z.of_nat (4 * 2) +ᵢ
    ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4)))))) = $ 32) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.
  assert ((i0 +ᵢ  $ 36) +ᵢ  Int.mul i ($ 65536) =   ((((((((i0 +ᵢ  Int.mul i ($ 65536)) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4)
           +ᵢ  $ Z.of_nat (4 * 2)) +ᵢ  $ Z.of_nat 4) +ᵢ  
         $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  $ Z.of_nat 4) +ᵢ  
      $ Z.of_nat 4).
  { do 9 rewrite Int.add_assoc.
    assert (  ($ Z.of_nat 4 +ᵢ
  ($ Z.of_nat 4 +ᵢ
   ($ Z.of_nat (4 * 2) +ᵢ
    ($ Z.of_nat 4 +ᵢ
     ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4)))))))= $ 36) by mauto.
    rewrite H.
    rewrite (Int.add_commut (Int.mul i ($ 65536))).
    auto. }
  rewrite H;clear H.

  split;intros.
  + 
    sep normal in H.
    sep destruct H.
    sep split in H.
    rewrite H0 in *.
    cbn [firstn].
    cbn [nth_error val_inj pre28bits'].
    sep split;auto.
    cbn [firstn Astruct' typelen fst snd] in *.
    sep normal.
    apply H.

    simpl; tauto.
    eexists;eauto.
  + sep split in H.
    do 11 (destruct tmri;tryfalse).
    cbn [firstn] in *.
    destruct H3 as [? [? [? [? [? [? [? [? ?]]]]]]]].
    destruct v;tryfalse.
    destruct v0;tryfalse.
    destruct v2;tryfalse.
    destruct v3;tryfalse.
    destruct v4;tryfalse.
    destruct v5;tryfalse.
    destruct v6;tryfalse.
    destruct v7;tryfalse.
    cbn in H1.
    destruct H1;subst v8.
    cbn [nth_error val_inj pre28bits'] in *.
    cbn [firstn Astruct' typelen fst snd] in *.
    sep normal in H.

    sep normal.
    do 10 eexists.
    sep split;[apply H | eauto| eauto].
Qed.

Lemma Astruct_imply_AOSTMRNode_frm : 
forall i tmri p x,
length tmri = 10%nat ->
val_inj (nth_error tmri 9) = Vint32 x ->
pre28bits' (val_inj (nth_error tmri 8)) = Int.zero ->
struct_type_vallist_match OSTimerRegs (firstn 9 tmri) ->
Astruct (get_off_addr tmrRegsAddr (Int.mul i ($ 65536)))
          OSTimerRegs  (firstn 9 tmri)  **
PV timer_WDTCR i @ Int32u |-> val_inj (nth_error tmri 9) ** p ==>
AOSTMRNode i tmri ** p.
Proof.
  intros.
  pose proof AOSTMRNode_Astruct_frm i tmri p.
  eapply H4.
  sep auto.
  eexists;eauto.
Qed.

Lemma OS_timerConfigProofPart1: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'1: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV prdlo @ Int32u |-> Vint32 v'1 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSPRDLO =ₑ prdlo ′
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 5 tmri (Vint32 v'1)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV prdlo @ Int32u |-> Vint32 v'1 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.

  (*
  eapply assign_rule_struct_aop_typeneq. 
  Ltac t1 := let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H;  exact H .
  t1.
  Ltac t2:= (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto.
  t2.
  t2.
  simpl; auto.
  simpl; auto.
  unfold id_nth; simpl; auto.
  simpl; auto.
  intros; intro; tryfalse.
  intros; intro; tryfalse.
  intros; intro; tryfalse.
  symbolic execution.
  apply assign_type_match_true; simpl; auto.
  rewrite firstn_length_le; lia.
  eauto.
  intros; sep auto.
*)

  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  |
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }


  intros.
  erewrite update_nth_val_firstn in H5 by lia.
  erewrite <- (nth_error_update_nth_val 5%nat _ (Vint32 v'1)) in H5 by lia.
  sep lifts (3::4::nil)%nat in H5.
  eapply Astruct_imply_AOSTMRNode_frm in H5;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H4.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart2: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'2: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV prdhi @ Int32u |-> Vint32 v'2 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSPRDHI =ₑ prdhi ′
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 6 tmri (Vint32 v'2)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV prdhi @ Int32u |-> Vint32 v'2 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H5 by lia.
  erewrite <- (nth_error_update_nth_val 6%nat _ (Vint32 v'2)) in H5 by lia.
  sep lifts (3::4::nil)%nat in H5.
  eapply Astruct_imply_AOSTMRNode_frm in H5;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H4.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart3: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSCNTLO =ₑ ′ 0
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 3 tmri (Vint32 ($ 0))) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H5 by lia.
  erewrite <- (nth_error_update_nth_val 3%nat _ (Vint32 ($ 0))) in H5 by lia.
  sep lifts (3::4::nil)%nat in H5.
  eapply Astruct_imply_AOSTMRNode_frm in H5;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H4.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart4: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSCNTHI =ₑ ′ 0
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 4 tmri (Vint32 ($ 0))) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H5 by lia.
  erewrite <- (nth_error_update_nth_val 4%nat _ (Vint32 ($ 0))) in H5 by lia.
  sep lifts (3::4::nil)%nat in H5.
  eapply Astruct_imply_AOSTMRNode_frm in H5;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H4.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart5_modeneq0: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'3: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
Int.eq Int.zero v'3 = false ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV mode @ Int32u |-> Vint32 v'3 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSTCRreg =ₑ ′128
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 7 tmri (V$ tmrmode_config v'3)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV mode @ Int32u |-> Vint32 v'3 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  unfold tmrmode_config.
  rewrite H1.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H6 by lia.
  erewrite <- (nth_error_update_nth_val 7%nat _ (Vint32 ($ 128))) in H6 by lia.
  sep lifts (3::4::nil)%nat in H6.
  eapply Astruct_imply_AOSTMRNode_frm in H6;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H5.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart5_modeeq0: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'3: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
Int.eq Int.zero v'3 = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV mode @ Int32u |-> Vint32 v'3 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSTCRreg =ₑ ′64
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 7 tmri (V$ tmrmode_config v'3)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV mode @ Int32u |-> Vint32 v'3 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  unfold tmrmode_config.
  rewrite H1.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H6 by lia.
  erewrite <- (nth_error_update_nth_val 7%nat _ (Vint32 ($ 64))) in H6 by lia.
  sep lifts (3::4::nil)%nat in H6.
  eapply Astruct_imply_AOSTMRNode_frm in H6;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  rewrite nth_error_update_nth_val by lia;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H5.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart5_64bitneq0: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'4: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
Int.eq Int.zero v'4 = false ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV enable64bit @ Int32u |-> Vint32 v'4 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSTGCR =ₑ ′0
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 8 tmri (V$ enable64bit_config v'4)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV enable64bit @ Int32u |-> Vint32 v'4 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  unfold enable64bit_config.
  rewrite H1.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H6 by lia.
  erewrite <- (nth_error_update_nth_val 8%nat _ (Vint32 ($ 0))) in H6 by lia.
  sep lifts (3::4::nil)%nat in H6.
  eapply Astruct_imply_AOSTMRNode_frm in H6;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  unfold pre28bits' in H4.
  destruct (nth_error tmri 8) as [? | ] eqn:?;[cbn [val_inj] in H4 | tryfalse].
  destruct v;tryfalse.
  erewrite nth_error_update_nth_val_eq;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H5.
  simpl in *.
  tauto.
Qed.

Lemma OS_timerConfigProofPart5_65biteq0: forall 
r ri P
(ct: tid)
(v': val)
(tmrid_i v'4: int32) tmri
(aop: absop),
Int.ltu ($ 0) tmrid_i = true ->
Int.ltu tmrid_i ($ 16) = true ->
Int.eq Int.zero v'4 = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i tmri **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV enable64bit @ Int32u |-> Vint32 v'4 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}
timerx ′ → OSTGCR =ₑ ′4
{{ <|| aop ||>  **
  AOSTMRNode tmrid_i (update_nth_val 8 tmri (V$ enable64bit_config v'4)) **
  LV timerx @ OSTimerRegs ∗
  |-> Vptr (get_off_addr tmrRegsAddr (Int.mul tmrid_i ($ 65536))) **
  LV enable64bit @ Int32u |-> Vint32 v'4 **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((enable64bit, Int32u)
     :: (mode, Int32u)
        :: (prdhi, Int32u)
           :: (prdlo, Int32u)
              :: (os_code_defs.timerid, Int32u)
                 :: (timerx, OSTimerRegs ∗) :: nil) ** P }}.
Proof.
  intros.
  unfold enable64bit_config.
  rewrite H1.
  hoare lift 2%nat pre.
  eapply backward_rule1.
  eapply AOSTMRNode_Astruct_frm.
  pure intro.
  eapply forward_rule2.
  hoare lifts (3::4::1::nil)%nat pre.
  eapply assign_rule_struct_aop_typeneq;
  [ let s :=fresh "s" in let H:=fresh "H" in intro s; split; intro H; exact H
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic execution
  | apply assign_type_match_true; simpl; auto
  | 
  | reflexivity
  | li_sepauto li ].
  { rewrite firstn_length_le; lia. }

  intros.
  erewrite update_nth_val_firstn in H6 by lia.
  erewrite <- (nth_error_update_nth_val 8%nat _ (Vint32 ($ 4))) in H6 by lia.
  sep lifts (3::4::nil)%nat in H6.
  eapply Astruct_imply_AOSTMRNode_frm in H6;eauto.

  sep auto.
  rewrite update_nth_val_len_eq;auto.
  rewrite nth_error_update_nth_val by lia;eauto.
  unfold pre28bits' in H4.
  destruct (nth_error tmri 8) as [? | ] eqn:?;[cbn [val_inj] in H4 | tryfalse].
  destruct v;tryfalse.
  erewrite nth_error_update_nth_val_eq;eauto.

  do 11 (destruct tmri;tryfalse).
  clear - H5.
  simpl in *.
  tauto.
Qed.