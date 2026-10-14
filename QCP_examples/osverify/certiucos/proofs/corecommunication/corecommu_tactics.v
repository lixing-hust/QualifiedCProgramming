Require Import ucos_include.
Require Import Lia.
Require Import symbolic_lemmas.
Require Import sep_auto.

Require Import aux_pureLib.
Require Import corecommu_rules.


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
  good_frm_sovler.
Qed.

#[export] Hint Resolve   good_frm_plocal: good_frm_lemmas.



Ltac afalse_tryfalse :=
  repeat match goal with 
  | H: (0 = 1)%nat |- _  => inversion H 
  | H: ?s |= Afalse |- _ => apply (astar_l_afalse_intro ([| (0 = 1)%nat |])) in H;sep split in H 
  | H : ?s |= Afalse ** _ |- _ => apply astar_l_afalse_elim in H 
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
                  try sep cancel EvtInv;
                  try sep cancel p_local.

Ltac find_evar' n x Hp :=
  match Hp with
    | ?A ** ?B =>
          match A with
          | LV x @ _ |-> _ => constr:(n)
          | GV x @ _ |-> _ => constr:(n)
          | _ => find_evar' (S n) x B
          end
   | LV x @ _ |-> _ => constr:(n)
   | GV x @ _ |-> _ => constr:(n)
   | _ => constr : (1%nat)
   end.

Ltac find_evar x Hp :=
 let y := find_evar' 1%nat x Hp in
 eval compute in y.

Ltac find_abs' n Hp :=
  match Hp with
    | ?A ** ?B =>
          match A with
          | Aop _ => constr:(n)
          | _ => find_abs' (S n) B
          end
   | Aop _ => constr:(n)
   | _ => constr : (1%nat)
   end.

Ltac find_abs Hp :=
 let y := find_abs' 1%nat Hp in
 eval compute in y.
 
Ltac find_name' n x Hp :=
  match Hp with
    | ?A ** ?B =>
          match A with
          | context[x] => constr:(n)
          | _ => find_name' (S n) x B
          end
   | context[x] =>constr:(n)
   | _ => constr : (1%nat)
   end.

Ltac find_name x Hp :=
 let y := find_name' 1%nat x Hp in
 eval compute in y.

Tactic Notation "sep" "evar" "lift" constr(x) "in" hyp (H):=
  match type of H with
  | sat _ ?P => let n:= find_evar x P in
                       sep lift n in H
  | _ =>idtac
  end. 
  
Tactic Notation "sep" "evar" "lift" constr(x)  :=
  match goal with
  | |- sat _ ?P => let n:= find_evar x P in
                             sep lift n 
  | _ =>idtac
  end. 
  
Tactic Notation "sep" "name" "lift" constr(x) "in" hyp (H):=
  match type of H with
  | sat _ ?P => let n:= find_name x P in
                          sep lift n in H
  | _ =>idtac
  end. 
  
Tactic Notation "sep" "name" "lift" constr(x)  :=
  match goal with
  | |- sat _ ?P => let n:= find_name x P in
                               sep lift n 
  | _ =>idtac
  end. 

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) "in" hyp(H):=
  sep name lift H2 in H;
  sep name lift H1 in H.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3) "in" hyp(H):=
  sep name lift H3 in H;
  sep name lift H2 in H;
  sep name lift H1 in H.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4) "in" hyp(H):=
  sep name lift H4 in H;
  sep name lift H3 in H;
  sep name lift H2 in H;
  sep name lift H1 in H.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) "in" hyp(H):=
  sep name lift H5 in H;
  sep name lift H4 in H;
  sep name lift H3 in H;
  sep name lift H2 in H;
  sep name lift H1 in H.


Tactic Notation "sep" "name" "lift" constr(H1) constr(H2):=
  sep name lift H2;
  sep name lift H1.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3):=
  sep name lift H3;
  sep name lift H2;
  sep name lift H1.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4):=
  sep name lift H4;
  sep name lift H3;
  sep name lift H2;
  sep name lift H1.

Tactic Notation "sep" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5):=
  sep name lift H5;
  sep name lift H4;
  sep name lift H3;
  sep name lift H2;
  sep name lift H1.  


Tactic Notation "sep" "abs" "lift" "in" hyp (H):=
  match type of H with
  | sat _ ?P => let n:= find_abs P in
                       sep lift n in H
  | _ =>idtac
  end. 
  
Tactic Notation "sep" "abs" "lift"  :=
  match goal with
  | |- sat _ ?P => let n:= find_abs P in
                             sep lift n 
  | _ =>idtac
  end. 

Tactic Notation "hoare" "abs" "lift" "pre" :=
  match goal with
  | |- InfRules _ _ _ _ _ _ ?P _ _ _ =>  let n:= find_abs P in  hoare lift n pre
  | _ => idtac
  end.
  
Tactic Notation "hoare" "evar" "lift" constr (x) "pre" :=
  match goal with
  | |- InfRules _ _ _ _ _ _ ?P _ _ _ => let n:= find_evar x P in hoare lift n pre
  | _ => idtac
  end.
  
Tactic Notation "hoare" "name" "lift" constr (x) "pre" :=
  match goal with
  | |- InfRules _ _ _ _ _ _ ?P _ _ _ => let n:= find_name x P in hoare lift n pre
  | _ => idtac
  end.

Ltac hoare_lift_evars_pre' l:=
  match l with
  | nil => idtac
  | ?x::?l' => hoare evar lift x pre; hoare_lift_evars_pre' l'
 end.
  
Tactic Notation "hoare" "evars" "lift" constr (l) "pre" :=
  let l':= (eval simpl rev in (rev l)) in hoare_lift_evars_pre' l'.
  
Tactic Notation "hoare" "critical" "lift" "pre":=
  hoare name lift A_dom_lenv pre; 
  hoare name lift A_isr_is_prop pre;
  hoare name lift Aisr pre;
  hoare name lift Acs pre;
  hoare name lift Ais pre;
  hoare name lift Aie pre.

Tactic Notation "hoare" "name" "lift" constr(H1) constr(H2) "pre" :=
  hoare name lift H2 pre;
  hoare name lift H1 pre.

Tactic Notation "hoare" "name" "lift" constr(H1) constr(H2) constr(H3) "pre" :=
  hoare name lift H3 pre;
  hoare name lift H2 pre;
  hoare name lift H1 pre.

Tactic Notation "hoare" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4) "pre" :=
  hoare name lift H4 pre;
  hoare name lift H3 pre;
  hoare name lift H2 pre;
  hoare name lift H1 pre.

Tactic Notation "hoare" "name" "lift" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) "pre" :=
  hoare name lift H5 pre;
  hoare name lift H4 pre;
  hoare name lift H3 pre;
  hoare name lift H2 pre;
  hoare name lift H1 pre.
  
Ltac init_solve_abort:=
  repeat (match goal with
  | |- context [  
    match ?l with
    | _ => _
    end
  ] => destruct l;hoare abs lift pre; try apply absabort_rule
  end).

Ltac find_lenv Hp :=
  match Hp with
    | ?A ** ?B =>
          match A with
          | A_dom_lenv _ => A
          | _ => find_lenv B
          end
    | A_dom_lenv _ => Hp
    | _ => Afalse
  end.


Ltac find_prop' n x Hp :=
    match Hp with
      | x => constr:(n)
      | x ** ?B => constr:(n)
      | _ ** ?B => find_prop' (S n) x B
      | _ => constr : (0%nat)
      end.
  
Ltac find_prop x Hp :=
   let y := find_prop' 1%nat x Hp in
   eval compute in y.

Ltac nth_sep n P:=
  match n with
  | O => None
  | S 0 => match P with
         | ?A ** _ => constr:(Some A)
         | _ => constr:(Some P)
         end
  | S ?n' => match P with
              | _ ** ?B => nth_sep n' B
              | _ => constr:(None)
              end
  end.
             
Ltac sep_autocancel_aux1 n :=
  match goal with
  | H: ?s |= ?Q |-?s |= ?P => 
      let p:= nth_sep n P in
      match p with
      | Some ?q => let m:= find_prop q Q in 
                    match m with
                    | O => sep_autocancel_aux1 (S n)
                    | S _ => sep cancel m n; sep_autocancel_aux1 n
                    end
      | None => idtac
      end
  | _ => idtac
  end.

Ltac sep_autocancel_aux2 n :=
  match goal with
  | H: ?s |= ?Q |-?s |= ?P => 
      let p:= nth_sep n P in
      match p with
      | Some ?q => 
        match q with
        | ?f ?e1 ?e2 ?e3 ?e4 ?e5 => first [sep cancel (f e1 e2 e3 e4); sep_autocancel_aux2 n | sep cancel (f e1 e2 e3); sep_autocancel_aux2 n | sep cancel (f e1 e2); sep_autocancel_aux2 n | sep cancel (f e1); sep_autocancel_aux2 n | sep cancel f; sep_autocancel_aux2 n | sep_autocancel_aux2 (S n)]
        | ?f ?e1 ?e2 ?e3 ?e4 => first [sep cancel (f e1 e2 e3); sep_autocancel_aux2 n | sep cancel (f e1 e2); sep_autocancel_aux2 n | sep cancel (f e1); sep_autocancel_aux2 n | sep cancel f; sep_autocancel_aux2 n | sep_autocancel_aux2 (S n)]
        | ?f ?e1 ?e2 ?e3 => first [sep cancel (f e1 e2); sep_autocancel_aux2 n | sep cancel (f e1); sep_autocancel_aux2 n | sep cancel f; sep_autocancel_aux2 n | sep_autocancel_aux2 (S n)]
        | ?f ?e1 ?e2 => first [sep cancel (f e1); sep_autocancel_aux2 n | sep cancel f; sep_autocancel_aux2 n | sep_autocancel_aux2 (S n)]
        | ?f ?e1 => first [sep cancel f; sep_autocancel_aux2 n | sep_autocancel_aux2 (S n)]
        end
      | None => idtac
      end
  | _ => idtac
  end.

Ltac sep_autocancel:= trycancel; sep_autocancel_aux1 1%nat; sep_autocancel_aux2 1%nat.

Tactic Notation "sep" "autocancel":= sep_autocancel.
               
Ltac invertsr Hp:=
  match type of Hp with
  | _ = _ => symmetry in Hp; inverts Hp
  | _ => inverts Hp
  end.

Ltac hoare_calle_lvar_logicl l:=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |-?ct {{ ?P }} scalle (evar ?x) _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n => 
          let e:= find_lenv P in
          hoare abs lift pre; 
            eapply calle_rule_lvar'_twop with (logicl:=l) (p2:=e); 
            [ intuition eauto  | 
              intros; do 5 try 
                          (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;unfold_spec; sep auto |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ]
        | none _ => idtac 
      end
  end.

(* Much quicker than the normal version, a bit less automation *)
Ltac hoare_calle_lvar_logicl_fast l:=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |-?ct {{ ?P }} scalle (evar ?x) _ ?el {{ _ }} =>
        hoare abs lift pre; 
            eapply calle_rule_lvar' with (logicl:=l); 
            [ intuition eauto  | 
              intros; do 5 try 
                          (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;unfold_spec; sep normal; sep eexists; sep autocancel |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ]
  end.

  Ltac hoare_call_logicl l :=
    match goal with
      | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
        match find_aop P with 
          | some ?n =>  
                let e:= find_lenv P in
                  hoare abs lift pre; 
                  eapply call_rule'_twop with (logicl:=l)(p2:=e);
                  [intuition eauto | 
                   intros; 
                      do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                       first [apply rvl_nil | simpl;auto] |
                   intros;unfold_spec; sep auto |
                   idtac |
                   sep_unfold_funpost |
                   sep_unfold_funpre |
                   simpl;eauto
                  ] 
          | none _ => idtac
        end
    end.

Ltac hoare_call_logicl_fast l :=
  match goal with
  | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
            hoare abs lift pre; 
              eapply call_rule' with (logicl:=l);
              [intuition eauto | 
                intros; 
                  do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                    first [apply rvl_nil | simpl;auto] |
                intros;unfold_spec; sep normal; sep eexists; sep autocancel |
                idtac |
                sep_unfold_funpost |
                sep_unfold_funpre |
                simpl;eauto
              ] 
  end. 

Ltac sep_pauto'' := 
  repeat progress match goal with 
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
        | context [Aisr] => sep name lift Aisr in H; apply astar_l_aisr_elim in H as [? H]   end 
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
      | context [Aier] => sep name lift Aier in H; apply astar_l_aier_elim in H as [? H] end
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
      | context [Ais] => sep name lift Ais in H; apply astar_l_ais_elim in H as [? H] end
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
      | context [Acs] => sep name lift Acs in H; apply astar_l_acs_elim in H as [? H] end
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
      | context [Aie] => sep name lift Aie in H; apply astar_l_aie_elim in H as [? H] end
  | H: ?s |= ?p |- ?s |= ?q =>  match p with 
      | context [Aop] => sep name lift Aop in H; apply astar_l_aop'_elim in H as [? H] end
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
        | context [Aisr] => sep name lift Aisr; apply astar_l_aisr_intro ;eauto  end 
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
      | context [Aier] => sep name lift Aier; apply astar_l_aier_intro ;eauto end
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
      | context [Ais] => sep name lift Ais; apply astar_l_ais_intro ;eauto end
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
      | context [Acs] => sep name lift Acs; apply astar_l_acs_intro ;eauto end
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
      | context [Aie] => sep name lift Aie; apply astar_l_aie_intro ;eauto end
  | H: ?s |= ?p |- ?s |= ?q =>  match q with 
      | context [Aop] => sep name lift Aop; apply astar_l_aop'_intro ;eauto end
  end.

Ltac sep_pauto' := sep pauto;  sep_pauto''.

(* Only intros existential variables and pure facts in preconditions *)
Ltac naive_pure_intro:=
  hoare normal pre;
  repeat (apply ex_intro_rule; intros); 
  repeat (hoare name lift Apure pre; apply pure_split_rule'; intros).

Tactic Notation "naive" "pure" "intro":= naive_pure_intro.