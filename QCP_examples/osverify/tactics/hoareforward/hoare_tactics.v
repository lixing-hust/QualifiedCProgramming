Require Import Coq.Bool.IfProp.
Require Import Coq.Logic.Classical_Prop.
Require Import Recdef.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import include_frm.
Require Import sep_auto.
Require Import hoare_conseq.
Require Import derived_rules.
Require Import hoare_assign.
Require Import hoare_if.
Require Import hoare_ret.
Require Import hoare_call.
Require Import cancel_abs.
Set Implicit Arguments.                                                                                                                                                                                                              
(* function call *)

Ltac hoare_split_pure n :=
  hoare lift n pre;
  apply pure_split_rule'; intro.

Ltac hoare_intro_pure n :=
  hoare lift n pre;
  apply pure_intro_rule'; intro;
  hoare lower 1%nat pre.

Ltac hoare_cut_pure x :=
  apply prop_elim_rule1 with x;
  [ repeat (apply pure_ex_intro_rule; first [ apply ex_intro_rule' | apply ex_intro_rule ]; intro)
  | intros; idtac ].

Ltac hoare_split_pure_all' :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
      match find_apure P with
        | some ?n => hoare_split_pure n; hoare_split_pure_all'
        | none _ => idtac
      end
  end.

Ltac hoare_ex_intro :=
  repeat match goal with
         | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
           first [ apply ex_intro_rule' ; intros
                 | apply ex_intro_rule; intros ]
         end.

Ltac hoare_split_pure_all :=
  hoare normal pre; hoare_ex_intro; hoare_split_pure_all'.

Ltac hoare_assert_pure x :=
  apply prop_elim_rule2 with x;
  [ intros; idtac
  | repeat (apply pure_ex_intro_rule; first [ apply ex_intro_rule' | apply ex_intro_rule ]; intro) ].

(*
Ltac move_aop_last :=
  match goal with
    | H:_ |- {|_ , _, _, _|}|- {{?p}}_ {{_}} =>
      match find_aop p with
        | some ?n => hoare lower n%nat pre
        | none => fail "No aop"
      end
    | _ => idtac
  end.
*)

Ltac array_leneq :=
  match goal with
  | H:_ |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | Aarray _ (Tarray ?t ?n) ?vl ** ?A =>
           first [ let x:= fresh in 
                   assert (length vl = n) as x by auto;
                     clear x  
                 | hoare_assert_pure (length vl = n);
                   [ eapply  array_length_intro; eauto
                   | hoare_split_pure_all]]
        |_  => idtac 
      end; hoare lower 1%nat pre
  end.

Ltac array_leneq_n n :=
  match n with
    | S ?n' => array_leneq;  array_leneq_n n'
    | _ => idtac
  end.

Ltac array_leneq_intro :=
  match goal with
    | H:_ |- {|_ , _, _, _, _, _|}|-_ {{?p}}_ {{_}} =>
      let lg := asrt_to_list p in
      let n:= (eval compute in (length lg)) in  array_leneq_n n
  end.

Ltac unfold_funpost :=
  match goal with
    | H:_
      |- {|_ , _, _, _, _, _|}|- _ {{?p}}_ {{_}} =>
      match p with
        | EX _,  POST  [?t, _, _ ,_ ,_] ** _=> 
          unfold getasrt;unfold t;
          match goal with
            | H:_
              |- {|_ , _, _, _, _, _|}|-_ {{?p}}_ {{_}} =>
              match p with
                | EX _,  (?t _ _ _ _) ** _=> 
                  unfold t
              end
          end
      end
  end.

Ltac elim_nil :=
  match goal with
    | H :  (length ?v > 0)%nat |- _ => destruct v; simpl in H;
                                        [false;  inverts H  | idtac]
    | H :  nth_val 0 ?v  = Some _ |- _ => destruct v; 
                                         [simpl in H ; false;  inverts H  |  idtac]
    | _ => idtac                                       
   end.

Tactic Notation "elim" "nil" := elim_nil.

Ltac find_aisr' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aisr' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aisr' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aisr _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aisr Hp :=
  let y := find_aisr' Hp in
  eval compute in y.

Ltac find_aier' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aier' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aier' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aier _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aier Hp :=
  let y := find_aier' Hp in
  eval compute in y.

Ltac find_aie' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_aie' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_aie' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Aie _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_aie Hp :=
  let y := find_aie' Hp in
  eval compute in y.

Ltac find_ais' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_ais' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_ais' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Ais _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_ais Hp :=
  let y := find_ais' Hp in
  eval compute in y.

Ltac find_acs' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_acs' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_acs' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | Acs _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_acs Hp :=
  let y := find_acs' Hp in
  eval compute in y.

(*
Ltac retpost_funs :=
  try (apply retpost_qptrsearch)(*;try (apply retpost_eventrdy);try (apply retpost_eventwait)*).
 *)

Ltac find_pre' Hp :=
  match Hp with
    | ?A ** ?B =>
      match find_pre' A with
        | some ?a => constr:(some a)
        | none ?a =>
          match find_pre' B with
            | some ?b => constr:(some (a + b)%nat)
            | none ?b => constr:(none (a + b)%nat)
          end
      end
    | getasrt _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_pre Hp :=
  let y := find_pre' Hp in
  eval compute in y.

 (* abstract consequence rule *)

Ltac hoare_abscsq :=
  match goal with
   | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
     match find_aop P with
      | none _ =>
         idtac 1 "no absop in the pre-condition"; fail 1
      | some ?a =>
      match find_absdata P absecblsid with
      | none _ => idtac;  hoare lift a pre; eapply abscsq_rule' 
      | some ?b => 
      match find_absdata P abstcblsid with
      | none _ => idtac 3 " no Habstcblsid in the pre-condition "; fail 3
       | some ?c => 
      match find_absdata P ostmid with
      | none _ => idtac 4 " no HTime in the pre-condition "; fail 4
       | some ?d => 
      match find_absdata P curtid with
      | none _ => idtac 5 " no HCurTCB in the pre-condition "; fail 5
       | some ?e => 
      match find_absdata P ierid with
      | none _ => idtac 6 " no Hierid in the pre-condition "; fail 6
       | some ?f => 
      match find_absdata P inthandlerid with
      | none _ => idtac 7 " no Hinthandlerid in the pre-condition "; fail 7
       | some ?g => 
      match find_absdata P inthandlerParamid with
      | none _ => idtac 8 " no HinthandlerParamid in the pre-condition "; fail 8
       | some ?h => 
      match find_absdata P exchandlerid with
      | none _ => idtac 9 " no Hexchandlerid in the pre-condition "; fail 9
       | some ?i => 
      match find_absdata P absptlsid with
      | none _ => idtac 10 " no Habsptlsid in the pre-condition "; fail 10
       | some ?j => 
      match find_absdata P seminfoid with
      | none _ => idtac 11 " no Hseminfoid in the pre-condition "; fail 11
       | some ?k => 
      match find_absdata P absmutinfoid with
      | none _ => idtac 12 " no Habsmutinfoid in the pre-condition "; fail 12
       | some ?l => 
      match find_absdata P absmqattrid with
      | none _ => idtac 13 " no Habsmqattrid in the pre-condition "; fail 13
       | some ?m => 
      match find_absdata P pblsid with
      | none _ => idtac 14 " no Hpblsid in the pre-condition "; fail 14
       | some ?n => 
      match find_absdata P eblsid with
      | none _ => idtac 15 " no Heblsid in the pre-condition "; fail 15
       | some ?o => 
      match find_absdata P evatomheapid with
      | none _ => idtac 16 " no Hevatomheapid in the pre-condition "; fail 16
       | some ?p => 
      match find_absdata P evstructheapid with
      | none _ => idtac 17 " no Hevstructheapid in the pre-condition "; fail 17
       | some ?q => 
      match find_absdata P evarrayheapid with
      | none _ => idtac 18 " no Hevarrayheapid in the pre-condition "; fail 18
       | some ?r => 
      match find_absdata P evlocid with
      | none _ => idtac 19 " no Hevlocid in the pre-condition "; fail 19
       | some ?s => 
      match find_absdata P evptrid with
      | none _ => idtac 20 " no Hevptrid in the pre-condition "; fail 20
       | some ?t => 
      match find_absdata P ostmrid with
      | none _ => idtac 21 " no HTMRList in the pre-condition "; fail 21
       | some ?u => 
      match find_absdata P osclkrateid with
      | none _ => idtac 22 " no HClkRate in the pre-condition "; fail 22
       | some ?v => 
      match find_absdata P curcoreid with
      | none _ => idtac 23 " no Hcurcoreid in the pre-condition "; fail 23
       | some ?w => 
      match find_absdata P oscoreheapid with
      | none _ => idtac 24 " no Hcoreheapid in the pre-condition "; fail 24
       | some ?x => 
      match find_absdata P ipcsendid with
      | none _ => idtac 25 " no Hipcsendid in the pre-condition "; fail 25
       | some ?y => 
      match find_absdata P ipcrecvid with
      | none _ => idtac 26 " no Hipcrecvid in the pre-condition "; fail 26
       | some ?z => 
      match find_absdata P ipcsemid with
      | none _ => idtac 27 " no Hipcsemid in the pre-condition "; fail 27
       | some ?a' => 
      match find_absdata P ipcsendsemid with
      | none _ => idtac 28 " no Hipcsendsemid in the pre-condition "; fail 28
       | some ?b' => 
      match find_absdata P ipcsemshareid with
      | none _ => idtac 29 " no Hipcsemshareid in the pre-condition "; fail 29
       | some ?c' => 
      match find_absdata P ipcbroadid with
      | none _ => idtac 30 " no Hipcbroadid in the pre-condition "; fail 30
       | some ?d' => 
      match find_absdata P ipcgrid with
      | none _ => idtac 31 " no Hipcgrid in the pre-condition "; fail 31
       | some ?e' => 
          hoare lifts (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::q::r::s::t::u::v::w::x::y::z::a'::b'::c'::d'::e'::nil) pre; eapply abscsq_rule'
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
        end
   end
 end.

  Ltac hoare_abscsq' :=
    match goal with
      | |- {| _, _, _, _, _, _ |} |-_ {{ _ }} _ {{ ?P }} =>
        match find_aop P with
         | none _ =>
            idtac 1 "no absop in the post-condition"; fail 1
         | some ?a =>
         match find_absdata P absecblsid with
         | none _ => idtac;  hoare lift a post; eapply abscsq_rule''  
         | some ?b => 
         match find_absdata P abstcblsid with
         | none _ => idtac 3 " no Habstcblsid in the post-condition "; fail 3
          | some ?c => 
         match find_absdata P ostmid with
         | none _ => idtac 4 " no HTime in the post-condition "; fail 4
          | some ?d => 
         match find_absdata P curtid with
         | none _ => idtac 5 " no HCurTCB in the post-condition "; fail 5
          | some ?e => 
         match find_absdata P ierid with
         | none _ => idtac 6 " no Hierid in the post-condition "; fail 6
          | some ?f => 
         match find_absdata P inthandlerid with
         | none _ => idtac 7 " no Hinthandlerid in the post-condition "; fail 7
          | some ?g => 
         match find_absdata P inthandlerParamid with
         | none _ => idtac 8 " no HinthandlerParamid in the post-condition "; fail 8
          | some ?h => 
         match find_absdata P exchandlerid with
         | none _ => idtac 9 " no Hexchandlerid in the post-condition "; fail 9
          | some ?i => 
         match find_absdata P absptlsid with
         | none _ => idtac 10 " no Habsptlsid in the post-condition "; fail 10
          | some ?j => 
         match find_absdata P seminfoid with
         | none _ => idtac 11 " no Hseminfoid in the post-condition "; fail 11
          | some ?k => 
         match find_absdata P absmutinfoid with
         | none _ => idtac 12 " no Habsmutinfoid in the post-condition "; fail 12
          | some ?l => 
         match find_absdata P absmqattrid with
         | none _ => idtac 13 " no Habsmqattrid in the post-condition "; fail 13
          | some ?m => 
         match find_absdata P pblsid with
         | none _ => idtac 14 " no Hpblsid in the post-condition "; fail 14
          | some ?n => 
         match find_absdata P eblsid with
         | none _ => idtac 15 " no Heblsid in the post-condition "; fail 15
          | some ?o => 
         match find_absdata P evatomheapid with
         | none _ => idtac 16 " no Hevatomheapid in the post-condition "; fail 16
          | some ?p => 
         match find_absdata P evstructheapid with
         | none _ => idtac 17 " no Hevstructheapid in the post-condition "; fail 17
          | some ?q => 
         match find_absdata P evarrayheapid with
         | none _ => idtac 18 " no Hevarrayheapid in the post-condition "; fail 18
          | some ?r => 
         match find_absdata P evlocid with
         | none _ => idtac 19 " no Hevlocid in the post-condition "; fail 19
          | some ?s => 
         match find_absdata P evptrid with
         | none _ => idtac 20 " no Hevptrid in the post-condition "; fail 20
          | some ?t => 
         match find_absdata P ostmrid with
         | none _ => idtac 21 " no HTMRList in the post-condition "; fail 21
          | some ?u => 
         match find_absdata P osclkrateid with
         | none _ => idtac 22 " no HClkRate in the post-condition "; fail 22
          | some ?v => 
         match find_absdata P curcoreid with
         | none _ => idtac 23 " no Hcurcoreid in the post-condition "; fail 23
          | some ?w => 
         match find_absdata P oscoreheapid with
         | none _ => idtac 24 " no Hcoreheapid in the post-condition "; fail 24
          | some ?x => 
         match find_absdata P ipcsendid with
         | none _ => idtac 25 " no Hipcsendid in the post-condition "; fail 25
          | some ?y => 
         match find_absdata P ipcrecvid with
         | none _ => idtac 26 " no Hipcrecvid in the post-condition "; fail 26
          | some ?z => 
         match find_absdata P ipcsemid with
         | none _ => idtac 27 " no Hipcsemid in the post-condition "; fail 27
          | some ?a' => 
         match find_absdata P ipcsendsemid with
         | none _ => idtac 28 " no Hipcsendsemid in the post-condition "; fail 28
          | some ?b' => 
         match find_absdata P ipcsemshareid with
         | none _ => idtac 29 " no Hipcsemshareid in the post-condition "; fail 29
          | some ?c' => 
         match find_absdata P ipcbroadid with
         | none _ => idtac 30 " no Hipcbroadid in the post-condition "; fail 30
          | some ?d' => 
         match find_absdata P ipcgrid with
         | none _ => idtac 31 " no Hipcgrid in the post-condition "; fail 31
          | some ?e' =>
         match find_absdata P freedynid with
          | none _ => idtac 32 " no Hfreedyn in the post-condition "; fail 32
          | some ?f' =>
         match find_absdata P dynheapid with
          | none _ => idtac 33 " no Hdynheap in the post-condition "; fail 33
          | some ?g' => 
             hoare lifts (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::q::r::s::t::u::v::w::x::y::z::a'::b'::c'::d'::e'::f'::g'::nil) post; eapply abscsq_rule'' 
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
           end
      end
    end.

Tactic Notation "hoare" "abscsq" := hoare_abscsq.

Tactic Notation "hoare" "abscsq" "post" := hoare_abscsq'.

(* hoare forward *)

Ltac hoare_forward_first :=
  first [ hoare_assign
        | hoare_if
        | hoare_ret
        | hoare_call
        | hoare_calle_lvar
        | idtac ].

Ltac hoare_forward_stmts' :=
  let s := fresh in
  let H := fresh in
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
    eapply seq_rule; [ hoare_forward_stmts'
                     | idtac ]
  | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
    eapply forward_rule2; [ hoare_forward_first
                          | try sep_unfold_funpost;
                            first [ intros s H; exact H
                                  | sep pauto ] ]
  end.

Ltac hoare_forward_stmts :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_stmts'
  end.

Ltac hoare_forward_stmts'_nsepauto :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_stmts'_nsepauto
                       | idtac ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ hoare_forward_first
                            | ]
  end.

Ltac hoare_forward_stmts_nsepauto :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalse_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse }} _ {{ _ }} =>
      apply hoare_disj_afalse_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ Afalse ** ?P \\// _ }} _ {{ _ }} =>
      apply hoare_disj_afalseP_l_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// Afalse **?P }} _ {{ _ }} =>
      apply hoare_disj_afalseP_r_pre
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ \\// _ }} _ {{ _ }} =>
      eapply disj_rule
    | _ => hoare normal pre; hoare_ex_intro;  hoare_forward_stmts'_nsepauto
  end.

Tactic Notation "hoare" "forward" := hoare_forward_stmts.
