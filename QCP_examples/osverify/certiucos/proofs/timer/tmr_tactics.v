Require Import ucos_include.
Require Import Lia.
Require Import symbolic_lemmas.
Require Import sep_auto.

Require Import aux_pureLib.
Require Import corecommu_tactics.


Open Scope code_scope.

Open Scope int_scope.

Lemma good_frm_plocal:
  forall tid l, GoodFrm (p_local OSLInv tid l).
Proof.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  intros.
  go.
Qed.

#[export] Hint Resolve   good_frm_plocal: good_frm_lemmas.

Lemma good_frm_HeapInv':
  GoodFrm HeapInv'.
Proof.
  unfold HeapInv'.
  intros.
  go.
Qed.

#[export] Hint Resolve   good_frm_HeapInv': good_frm_lemmas.


Lemma can_change_aop_HeapInv':can_change_aop HeapInv'.
Proof. unfold HeapInv'; can_change_aop_solver. Qed.
#[export] Hint Resolve can_change_aop_HeapInv'  : can_change_aop.



Ltac afalse_tryfalse :=
  repeat match goal with 
  | H: (0 = 1)%nat |- _  => inversion H 
  | H: ?s |= Afalse |- _ => apply (astar_l_afalse_intro ([| (0 = 1)%nat |])) in H;sep split in H 
  | H : ?s |= Afalse ** _ |- _ => apply astar_l_afalse_elim in H 
  end.

Ltac hoare_abscsq_tmr1 :=
    match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
      match find_aop P with
       | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
       | some ?a =>
       match find_absdata P ostmid with
       | none _ => idtac 2 " no HTime in the pre-condition "; fail 2
        | some ?b => 
       match find_absdata P curtid with
       | none _ => idtac 3 " no HCurTCB in the pre-condition "; fail 3
        | some ?c => 
       match find_absdata P ostmrid with
       | none _ => idtac 4 " no HTMRList in the pre-condition "; fail 4
        | some ?d => 
       match find_absdata P osclkrateid with
       | none _ => idtac 5 " no HClkRate in the pre-condition "; fail 5
        | some ?e => 
           hoare lifts (a::b::c::d::e::nil) pre; eapply abscsq_rule'
         end
         end
         end
         end
    end
  end.

Ltac hoare_abscsq_tmr2 :=
  match goal with
  | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
    match find_aop P with
     | none _ =>
        idtac 1 "no absop in the pre-condition"; fail 1
     | some ?a =>
     match find_absdata P ostmid with
     | none _ => idtac 2 " no HTime in the pre-condition "; fail 2
      | some ?b => 
     match find_absdata P curtid with
     | none _ => idtac 3 " no HCurTCB in the pre-condition "; fail 3
      | some ?c => 
     match find_absdata P ostmrid with
     | none _ => idtac 4 " no HTMRList in the pre-condition "; fail 4
      | some ?d => 
     match find_absdata P osclkrateid with
     | none _ => idtac 5 " no HClkRate in the pre-condition "; fail 5
      | some ?e => 
     match find_absdata P oscoreheapid with
     | none _ => idtac 6 " no Hcoreheapid in the pre-condition "; fail 6
      | some ?f => 
         hoare lifts (a::b::c::d::e::f::nil) pre; eapply abscsq_rule'
       end
       end
       end
       end
       end
  end
end.


Ltac trycancel := try sep cancel Aisr;
                  try sep cancel Aie;
                  try sep cancel Ais;
                  try sep cancel Acs;
                  try sep cancel Aier;
                  try sep cancel AOSEventFreeList;
                  try sep cancel AOSQFreeList;
                  try sep cancel AOSQFreeBlk;
                  try sep cancel AOSTCBFreeList;
                  try sep cancel AECBList;
                  try sep cancel AOSMapTbl;
                  try sep cancel AOSUnMapTbl;
                  try sep cancel AOSTCBPrioTbl;
                  try sep cancel AOSIntNesting;
                  try sep cancel AOSTCBList;
                  try sep cancel AOSRdyTblGrp;
                  try sep cancel AOSTime;
                  try sep cancel AGVars;
                  try sep cancel AOSRdyTbl;
                  try sep cancel AOSRdyGrp;
                  try sep cancel tcbdllflag;
                  try sep cancel EvtInv;
                  try sep cancel APthreadAttr; (*new added *)                  
                  try sep cancel CapabilityInv; (* new added *)
                  try sep cancel HeapInv';
                  try sep cancel AOSTMRList';
                  try sep cancel AOSTMRList_TMRused;
                  try sep cancel AOSTMRNode;
                  try sep cancel AOSClkRate;
                  try sep cancel CoreCommuInv;
                  try sep cancel PartitionInv;
                  try sep cancel p_local.

Ltac hoare_call := eapply seq_rule; [ 
  eapply call_rule' ;[ 
  intuition eauto | 
             intros; 
                do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                 first [apply rvl_nil | simpl;auto] |
             intros;
             unfold_spec; sep normal; sep eexists; trycancel;sep pauto |
             go |
             sep_unfold_funpost |
             sep_unfold_funpre |
             simpl;eauto
            ]  |  
  unfold_funpost;pure intro ].

Ltac hoare_call_aempiser := eapply seq_rule; [ 
  eapply call_rule' ;[ 
  intuition eauto | 
             intros; 
                do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                 first [apply rvl_nil | simpl;auto] |
             let H := fresh "H" in 
             intros [[? ?] ?] H;
             sep name lift aemp_isr_is in H; eapply aemp_isr_elim in H;
             unfold_spec; sep normal; sep eexists; trycancel;sep pauto |
             go |
             sep_unfold_funpost |
             sep_unfold_funpre |
             simpl;eauto
            ]  |  
  unfold_funpost;pure intro;
  hoare name lift Aier pre;
  hoare name lift Ais pre;
  hoare name lift Aisr pre;
  eapply backward_rule1;[ eapply add_aemp_isr_is_prop | ] ].

Ltac hoare_calle_lvar_aempiser :=
eapply seq_rule; [ 
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |-?ct {{ ?P }} scalle (evar ?x) _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
          hoare lifts (n::nil)%nat pre; 
            eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              let H := fresh "H" in 
              intros [[? ?] ?] H;
              sep name lift aemp_isr_is in H; eapply aemp_isr_elim in H;
              unfold_spec; sep normal; sep eexists; trycancel;sep pauto |
              go |
              unfold retpost;
              let H := fresh "H" in intros * H;
                match goal with
              | H:  context [ POST [ ?x, _, _, _, _] ]  |-  _ =>
                unfold getasrt, x in H;
                match goal with
                  | H: ?s |= ?t' _ _ _ _ |- _ => unfold t' in H
                end
                end;
              sep destruct H; sep split in H; congruence |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ]
        | none _ => idtac
      end
  end | 
  unfold_funpost;pure intro;
  hoare name lift Aier pre;
  hoare name lift Ais pre;
  hoare name lift Aisr pre;
  eapply backward_rule1;[ eapply add_aemp_isr_is_prop | ] ].

