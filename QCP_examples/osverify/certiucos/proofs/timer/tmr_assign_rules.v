Require Import ucos_include.
Require Import Lia.

Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_tactics.

Open Scope code_scope.

Open Scope int_scope.

Definition tmrregsLists : list (int32 -> block * int32) := (timer_RSVD0::timer_EMUMGT_CLKSPD::timer_RSVD1::timer_RSVD1::timer_CNTLO::timer_CNTHI::timer_PRDLO::timer_PRDHI::timer_TCR::timer_TGCR::timer_WDTCR::nil).

Ltac unfold_funclist' l :=   
  match l with 
   | nil => idtac 
   | ?f :: ?l'' => try unfold f;unfold_funclist' l''
   end.

Ltac unfold_funclist l :=
  let l' := eval cbv delta [l]  in l  in
  unfold_funclist' l'.

Lemma timerregs_off_eq_shl : 
  forall n z b i0 i,
  (4 <= n <= 10)%nat ->
  z = Z.of_nat n ->
  tmrRegsAddr = (b, i0) ->
  Int.ltu i ($ 16) = true ->
  (b, (i0 +ᵢ  Int.mul ($ z) ($ 4)) +ᵢ  Int.mul (i<<ᵢ$ 14) ($ 4)) = (nth n tmrregsLists timer_RSVD0 i).
Proof.
  intros.
  assert ( Int.mul i ($ 16384) = i<<ᵢ$ 14 ).
  { eapply Int.mul_pow2;pauto.  } 
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  assert ( n= 4 \/ n= 5 \/ n= 6 \/ n= 7 \/ n=8 \/ n= 9 \/ n= 10)%nat by lia.
  clear H.
  destruct H5 as [ | [ | [ | [ | [ | [ | ]]]]] ];subst n;unfold tmrregsLists;cbn;
  unfold_funclist tmrregsLists;rewrite H1;
  unfold get_off_addr;cbn;
  match goal with 
  | |- (?b, ?i) = (?b, ?i0) => let H := fresh "H" in 
     assert (i = i0) as H;[ rewrite <- H3;rewrite Int.mul_assoc;rewrite H4
     | rewrite H;auto]
  end;
  match goal with 
  | |- (?a +ᵢ  ?b) +ᵢ ?c = (?a +ᵢ  ?b') +ᵢ ?c => 
  let H := fresh "H" in 
     assert (b = b') as H;[
     | rewrite H;auto]
  end;mauto.
Qed.

Lemma timerregs_off_eq_mul : 
  forall n z b i0 i,
  (n < 2 \/ 4 <= n <= 10)%nat ->
  z = Z.of_nat n ->
  tmrRegsAddr = (b, i0) ->
  Int.ltu i ($ 16) = true ->
  (b, (i0 +ᵢ  Int.mul ($ z) ($ 4)) +ᵢ  Int.mul (Int.mul i 
  ($ 16384)) ($ 4)) = (nth n tmrregsLists timer_RSVD0 i).
Proof.
  intros.
  assert (Int.mul ($ 16384) ($ 4) = ($ 65536)) by pauto.
  assert (n=0 \/ n=1 \/  n= 4 \/ n= 5 \/ n= 6 \/ n= 7 \/ n=8 \/ n= 9 \/ n= 10)%nat by lia.
  clear H.
  destruct H4 as [ | [ | [ | [ | [ | [ | [ | [ | ]]]]]]] ];subst n;unfold tmrregsLists;cbn;
  unfold_funclist tmrregsLists;rewrite H1;
  unfold get_off_addr;cbn;
  match goal with 
  | |- (?b, ?i) = (?b, ?i0) => let H := fresh "H" in 
     assert (i = i0) as H;[ rewrite Int.mul_assoc;rewrite H3
     | rewrite H;auto]
  end;
  match goal with 
  | H: z = Z_of_nat 0 |- (?a +ᵢ Int.mul ($ ?z) ($ 4)) +ᵢ ?c = ?a +ᵢ ?c => 
    subst z; let h := fresh "H" in  assert ($ (Z.of_nat 0%nat)  = Int.zero) as h by pauto;
    rewrite h;rewrite Int.mul_commut;rewrite Int.mul_zero;rewrite Int.add_zero;auto
  | |- (?a +ᵢ  ?b) +ᵢ ?c = (?a +ᵢ  ?b') +ᵢ ?c => 
  let H := fresh "H" in 
     assert (b = b') as H;[
     | rewrite H;auto]
  end;mauto.
Qed.
  
Lemma timer_assign_timerregs_shl : forall 
r ri aop ls 
(p':asrt )
(tid: tid)
(i : int32)
(v: val)
(vname: ident)
(n : nat)
(z : Z)
,
 (4 <= n <= 10)%nat ->
 z = Z.of_nat n ->
 Int.ltu i ($ 16) = true ->
 symbolic_lemmas.var_notin_dom __timerregs ls = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  **
  LV vname @ (Int32u) ∗ |-> v **
  GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv ls ** p' }} 
vname ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ z +ₑ (os_code_defs.timerid ′ ≪ ′ 14)) {{ 
<|| aop ||>   **
  LV vname @ (Int32u) ∗ |-> Vptr ((nth n tmrregsLists timer_RSVD0) i) **
  GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv ls ** p' }}.
Proof.
  intros.
  destruct tmrRegsAddr eqn: Htmraddr.
  eapply forward_rule2.
  {  hoare_assign.  }
  assert ( Int.ltu ($ 14) Int.iwordsize = true) by pauto.
  rewrite H3.
  cbn [val_inj].
  intros.
  erewrite timerregs_off_eq_shl in H4;eauto.
Qed.

Lemma timer_assign_timerregs_mul : forall 
r ri aop ls 
(p':asrt )
(tid: tid)
(i : int32)
(v: val)
(vname: ident)
(n : nat)
(z : Z)
,
 (n < 2 \/ 4 <= n <= 10)%nat ->
 z = Z.of_nat n ->
 Int.ltu i ($ 16) = true ->
 symbolic_lemmas.var_notin_dom __timerregs ls = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  **
  LV vname @ (Int32u) ∗ |-> v **
  GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv ls ** p' }} 
vname ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ z +ₑ (os_code_defs.timerid ′ × ′ 16384)) {{ 
<|| aop ||>   **
  LV vname @ (Int32u) ∗ |-> Vptr ((nth n tmrregsLists timer_RSVD0) i) **
  GV __timerregs @ (Tptr Tint32) |-> Vptr tmrRegsAddr **
  LV os_code_defs.timerid @ Int32u |-> Vint32 i **
  p_local OSLInv tid init_lg **
  A_dom_lenv ls ** p' }}.
Proof.
  intros.
  destruct tmrRegsAddr eqn: Htmraddr.
  eapply forward_rule2.
  { hoare_assign. }
  intros.
  erewrite timerregs_off_eq_mul in H3;eauto.
Qed.

Theorem ss_if_else_rule :
  forall Spec I r ri p q e tp s1 s2 v sc li ct,
    p ==> Rv e @ tp == v ->
    {| Spec, sc, I, r, ri, li|}|-ct {{ p ** [| v <> Vint32 Int.zero /\ v <> Vnull /\ v <> Vundef |] }} s1 {{ q }} ->
    {| Spec, sc, I, r, ri,li |}|-ct {{ p ** [| v = Vint32 Int.zero \/ v = Vnull |] }} s2 {{ q }} ->
  {| Spec, sc, I, r, ri,li |}|- ct {{ p }} sif e s1 s2 {{ q }}.
Proof.
  intros.
  eapply forward_rule2.
  eapply if_rule2';eauto.
  intros.
  destruct H2.
  sep auto.
  sep auto.
Qed.