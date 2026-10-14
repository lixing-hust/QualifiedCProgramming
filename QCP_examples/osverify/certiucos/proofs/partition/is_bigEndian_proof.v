Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.
Require Import pos_list_common.
Require Import ev_aux_code.
Require Import ifun_spec.
Require Import include_frm.
Require Import os_inv.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import init_spec.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward. (*change*)
Require Import math_auto.
Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import gjb_common.
Require Import abs_op.
Require Import include_frm.
Require Import NPeano.
Require Import ucos_pauto.
Require Import os_inv.
Require Import abs_infer_abt. 
Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Require Import partition_xml_init.
Require Import abs_op_partition_ext.
Require Import ifun_spec.

Open Scope code_scope.


Lemma is_bigEndian_proof:
    forall vl p r logicl ct, 
      Some p =  
      BuildPreI os_internal is_bigEndian vl logicl is_bigEndianPre ct->
      Some r =
      BuildRetI os_internal is_bigEndian vl logicl is_bigEndianPost ct->
      exists t d1 d2 s,
        os_internal is_bigEndian = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
eapply seq_rule. (*get one stmt*)          (* }                         *)
eapply forward_rule2.


(* let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _ ,_ |} |-?ct  {{ ?P }} (sassign (evar ?x) _) {{ _ }} =>
      match find_lvarmapsto P x with
        | some ?m =>
          match find_aop P with
            | none _ => fail 1
            | some ?n =>
              hoare lifts (n::m::nil)%list pre; (*将赋值变量和<|| v'1 ||>提到前面*)
               eapply assign_rule_lvar;  (*将要证明的东西拆开*)
                [ intro s; split; intro H; exact H
                | symbolic_execution
                | apply assign_type_match_true; simpl; auto | li_sepauto li]
          end
      end
  end.   *)

hoare_assign_var.                      (* }->这四句是提取一句出来code  *)
(* hoare_forward_first.  *)                    (* }                         *)
sep pauto.

eapply seq_rule.
(* eapply forward_rule2. *)
(* hoare_forward_first. *) (* problem happen in here, try to replace hoare_forward_first with other code*)
 let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _ ,_ |} |-?ct  {{ ?P }} (sassign (evar ?x) _) {{ _ }} =>
      match find_lvarmapsto P x with
        | some ?m =>
          match find_aop P with
            | none _ => fail 1
            | some ?n =>
              hoare lifts (n::m::nil)%list pre; (*将赋值变量和<|| v'1 ||>提到前面*)
              eapply assign_rule_lvar;  (*拆分证明目标*)
                [ intro s; split; intro H; exact H
                | eauto
                | apply assign_type_match_true; simpl; auto | li_sepauto li]             
          end
      end
  end.
2:intros.  (* symbolic_execution -> ?s |= Rv _ @ _ == _ => sep normal; sep eexists; sep get rv  *)
2:sep normal .
2:sep eexists.
1:intros.
unfold Alvarmapsto in H0 at 2.
sep normal in H0.
destruct H0.

eapply deref_rv.

eapply cast_rv_tptr.

2:{ instantiate(2:=long). simpl. auto. }

eapply addrof_lvar_rv. (* ????? *)

intros.
intros.
sep pauto. 
instantiate(3:= true). 
destruct_s s.

 instantiate(1 := PV(x, $1) @ char_t |->  (V$ 18) ** 
                  PV (x, $2) @ Int16u |-> (V$ 0) ** 
                  L& os_code_defs.a @ long == (x, Int.zero) **
                  LV b @ char_t |-> v'0 **
                  Aisr v'1 **
                  Aie v'2 **
                  Ais v'3 **
                  Acs v'4 **
                  Aier v'5 **
                  p_local OSLInv ct (logic_val (V$ 1) :: v'7) **
                  A_dom_lenv ((os_code_defs.a, long) :: (b, char_t) :: nil)%list ). 
 

unfold Aptrmapsto in *.
Local Open Scope list_scope. (*---------------------------------------------------------------------*)

sep remember (1 :: 2 :: 3 ::nil)%nat .
sep remember (2 ::nil)%nat in H0.

simpl in H0.
simpl.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
(* unfold mapstoval in H5. *)
destruct H6.
instantiate (1:= V$ 52).
unfolds in H6.
destruct H6.
destruct H6.
rewrite <-H6 in H9.
simpl in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
destruct H12.
destruct H13.
destruct H13.
destruct H13.
destruct H14.
destruct H15.
destruct H15.
destruct H15.
destruct H16.
1:{
do 6 eexists.
split.
auto.
split.
2:split.
3:split.
2:auto.
3:split.
instantiate(2:= x7).
join auto.
3: do 6 eexists.
3: split.
3:eauto.
3:split.
3:instantiate(2:= x9).
4:split.
rewrite -> H4 in H5.
eauto.
3:eauto.
2: instantiate(1:= (merge_list (x11 :: x13  :: x1 :: nil))).
2:{eapply join_comm.
join auto.
}
2:split.
3:split.
4:do 6 eexists.
4:split.
5:split.
6:split.
7:split.
split.
4:split.
10:split.
10:split.
2:eauto.
rewrite H8 in H5.
rewrite ->H4 in H5.
eapply map_join_emp'' in H5.
rewrite <-H5 in H4.

eapply join_emp in H4.


unfolds.
eexists.
split.
int auto.
simpl.
do 2 eexists.
split.
instantiate(2:= x7).
instantiate(1:= empenv).
join auto.
split.
2:eauto.
2:instantiate(2:= empenv ).
2:instantiate(1:= x4).
2:join auto.
3:join auto.
5:auto.
2:unfolds.
2:eexists.
2:split.
2:int auto.
unfold ptomval in *.
simpl.

int auto.
subst x7.
assert (Byte.repr 4660 = Byte.repr 52).
{
  eapply Byte.eqm_samerepr.
  unfold Byte.eqm.
  eapply Byte.eqm_same_bits.
  int auto.
  induction i3.
  simpl; auto.
  2:simpl; auto.
  destruct p.
+destruct p.
  -destruct p.  
    *destruct p. 
      simpl;auto.
      simpl;auto.
      simpl;auto.
    *destruct p.
      simpl;auto.
      simpl;auto.
      simpl;auto.
    *simpl;auto.
  -destruct p.
    *simpl;auto.
    *destruct p.
      simpl;auto.
      simpl;auto.
      simpl;discriminate.
    *simpl;auto.
  -simpl;auto.
+destruct p.
  -destruct p.
    *simpl;auto.
    *destruct p. 
      simpl;auto.
      simpl;auto.
      simpl;auto.
    *simpl;auto.
  -destruct p.
    *destruct p.
      simpl;auto.
      simpl;auto.
      simpl;discriminate.
    *destruct p.
      simpl;auto.
      simpl;auto.
      simpl;auto.
    *simpl;auto.
  -simpl;auto.
+simpl;auto.

}
rewrite H10.
eauto.
simpl.
do 2 eexists.
split.
instantiate(2:= x9 ).
instantiate(1:= empenv).
join auto.
split.
2:auto.
2:auto.
2:instantiate (2:=(merge_list (x11 :: x13  :: nil))).
2:instantiate (1:= x1).
2:join auto.
2:instantiate (2:= x3).
2:instantiate (1:= x4).
2:join auto.
3: auto.
int auto.
unfolds.
eexists.
split.
eauto.
simpl.
do 2 eexists.
split.
2:split.
3:do 2 eexists.
3:split.
4:split.
instantiate(2:= x11).
instantiate(1:= x13).
join auto.
int auto.
instantiate (2:= x13).
instantiate (1:=empenv).
join auto.
int auto.
auto.
sep auto.
sep auto.
}
eauto.
eauto.  
(*If (b ′ ==ₑ ′ 52){RETURN ′ 0}*)
hoare unfold.
hoare forward.
mytac_getret 1%nat.
hoare unfold.
hoare forward.
instantiate(1:= ($ 52)).
eauto.
hoare unfold.
hoare forward.
mytac_getret 2%nat.
hoare unfold.
hoare forward.
instantiate (1:= ($ 18)).
eauto.
Unshelve. 3: exact AMap.
Qed.