Require Import ucos_include.
Require Import seplog_tactics.
Require Import sem_lab.

(* specialized if else rule for solving ternary assignment *)
(* only allow nested ternary assignment in else-branch *)
Lemma wzy_if_else_rule : forall (Spec : funspec) pa ct (I : Inv) (r : retasrt)  (ri p q : asrt) (eb : expr) (tp : type) (s1 s2 : stmts) b sd
(t: type) x e v P,
  p ==> Rv eb @ tp == b ->
  p ==> Rv e @ tp == (V$ v) ->
  s1 = (sassign (evar x) e) ->
  {| Spec, sd, pa, I, r, ri |} |- ct
    {{ [|b <> Vint32 Int.zero /\ b <> Vnull /\ b <> Vundef|] ** p }}
    s1 {{ EX vx, [|vx = v|] ** LV x @ t |-> (V$ vx) ** q }} ->
  {|Spec , sd, pa, I, r, ri|} |-
    ct {{ [|b = Vint32 Int.zero \/ b = Vnull|] ** p }} s2
      {{ EX vx, [|P vx|] ** LV x @ t |-> (V$ vx) ** q }} ->
  {|Spec , sd, pa, I, r, ri|} |- ct {{ p }} (sif eb s1 s2)   
    {{ EX vx,
      [|(b <> Vint32 Int.zero /\ b <> Vnull /\ b <> Vundef /\ vx = v) \/
      ((b = Vint32 Int.zero \/ b = Vnull) /\ P vx) |] ** 
      LV x @ t |-> (V$ vx) ** q }}.
Proof.
  intros.
  eapply forward_rule1 with (q:=
    (
      [|b <> Vint32 Int.zero /\ b <> Vnull /\ b <> Vundef|] **
      EX vx : Z, [|vx = v|] ** LV x @ t |-> (V$ vx) ** q
    ) \\//
    (
      [|b = Vint32 Int.zero \/ b = Vnull|] **
      EX vx : Z, [|P vx|] ** LV x @ t |-> (V$ vx) ** q
    )
  );
  [intros ? [? | ?];[sep auto;left|sep auto;right]; tauto| ].
  eapply lzh_if_else_rule; auto.
Qed.

(* resolves ternary assignment (encoded as nested if-else) *)
(* TODO: currently only support nested ternary expression in the second branch *)
Ltac wzy_resolve_ternary_assign :=
  match goal with
  | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sif _ (sassign _ _) _) {{ _ }} => 
    eapply wzy_if_else_rule;
      [symbolic_execution;try pauto| |
        reflexivity | | ];
      [symbolic_execution;try pauto|
        hoare forward|wzy_resolve_ternary_assign ]
  | |- {| _ , _, _, _, _, _ |}|-?ct {{ _ }} (sassign _ _) {{ _ }} =>
    hoare forward;
    match goal with
    | |- _ ?v => instantiate (1:=fun vx => vx = v)
    end; simpl; auto
  | _ => fail "not a ternary expression assignment"
  end.


(* Lemma disj_merge_star_pure:
  forall P Q R S,
    (P ** [|Q|]) \\// (P ** [|R|]) \\// S ==>
    (P ** [|Q \/ R|]) \\// S.
Proof.
  intros.
  repeat apply adisj_elim in H as [? | ?].
  - left; sep auto.
  - left; sep auto.
  - right; sep auto.
Qed.

Lemma disj_false_r:
  forall P, P \\// [|False|] <==> P.
Proof.
  split; intros.
  - apply adisj_elim in H as [? | ?];
    sep auto; tryfalse.
  - left; auto.
Qed.

Lemma disj_merge_pure:
  forall P Q R,
    [|P|] ** [|Q|] ** R ==>
    [|P /\ Q|] ** R.
Proof.
  intros. sep auto.
Qed.

Lemma disj_impl_both:
  forall P Q P' Q',
    P ==> P' ->
    Q ==> Q' ->
    P \\// Q ==> P' \\// Q'.
Proof.
  intros.
  apply adisj_elim in H1 as [? | ?];
  [left|right]; auto.
Qed.

Ltac reshape_disj_clause H := idtac.

(* Ltac sep_disj_impl H :=
  match type of H with
  | _ |= _ \\// _ =>
      eapply disj_impl_both in H;
      [ | let H:= fresh "H" in intro H |
       ]
      
      (* let a:= fresh "a" in intro a *)
  end. *)

Ltac tac_lift_pure H :=
  match type of H with
  | _ |= _ ** ?P =>
    match find_apure P with
    | some ?n => sep lift (S n) in H
    | none => fail
    end
  end.

Ltac tac_merge_pure H :=
  repeat (tac_lift_pure H;
    apply disj_merge_pure in H).

Ltac tac_transform_disj_clause tac :=
  repeat eapply disj_impl_both;
  let H:= fresh "H" in
  intros ? H; tac H; exact H.

Lemma test:
  forall P Q,
  P ==> Q ->
  Q ==> [|False|] ->
  P ==> [|False|].
Admitted.

Goal forall P,
  ([| True |] ** P ** [| False |]) \\//
  ([| True |] ** P ** [| False |]) \\//
  ([| True |] ** P ** [| False |])
    ==>
  [|False|].
Proof.
  intros P.
  eapply test.

  tac_transform_disj_clause tac_merge_pure.

  eapply disj_impl_both in H;
  [ |
    let H:= fresh "H" in
    intros ? H; tac_merge_pure H; exact H
  | 
  
    (* tac_transform_disj_clause tac *)
  ].
  2:{
    eapply disj_impl_both.
  }
  
  eapply test.
  tac_transform_disj_clause tac_merge_pure.

  intros.
  .

  2:{}

  tac_transform_disj_clause H tac_merge_pure.
  tac_merge_pure H.
  .
  
  meta_find_and_lift_in_H_from_n
  (* apply adisj_elim in H as [Hl | Hr]. *)
    (* [idtac Hl | disj_map Hr tac]. *)
  disj_map H (meta_find_and_lift_in_H).
  eapply disj_impl_both in H;
  intro.
  sep_disj_impl H.

  disj_map H sep_auto. *)
