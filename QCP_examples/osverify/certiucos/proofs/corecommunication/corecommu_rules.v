Require Import os_spec.
Require Import os_inv.
(*Require Import ucos_code.*)
Require Import os_code_defs.
Require Import os_program.

Require Import include_frm.
Require Import abs_step.
Require Import base_tac.
Require Import hoare_forward.
Require Import math_auto.
Require Import sep_auto.
Require Import pure.
Require Import ucos_pauto.

Require Import abs_op_corecommu.
Require Import os_ucos_h.


Require Import Lia.

Open Scope code_scope.

Open Scope int_scope.

Lemma isptr_list_nth_ptr: 
  forall n i vl t, 
  length vl = n ->
  (i < n)%nat ->
  isvptr_list vl ->
  rule_type_val_match (t ∗)
  (nth_val' i vl) = true.
Proof. 
  induction n;intros.
  - simpl. inversion H0.
  - destruct vl;tryfalse.
  destruct i.
  cbn in *. destruct v;tryfalse. auto.
  cbn in H1. destruct v;tryfalse.
  apply lt_S_n in H0.
  inversion H.  
  specialize (IHn _ _ t H3 H0 H1). 
  cbn [nth_val'].
  auto.
Qed.

Lemma isptr_list_nth_ptr_ex: 
  forall n i vl , 
  length vl = n ->
  (i < n)%nat ->
  isvptr_list vl ->
  exists p, nth_val' i vl = Vptr p /\ In (Vptr p) vl.
Proof. 
  induction n;intros.
  - simpl. inversion H0.
  - destruct vl;tryfalse.
  destruct i.
  cbn in *. destruct v;tryfalse. exists a; auto.
  cbn in H1. destruct v;tryfalse.
  apply lt_S_n in H0.
  inversion H.  
  specialize (IHn _ _  H3 H0 H1). 
  cbn [nth_val']. 
  destruct IHn as [a0 [H2 H4]].
  eexists; split;eauto.
  eapply in_cons;auto.
Qed. 

Lemma DNUM_destruct :
    (DNUM = 0 \/ DNUM = 1 \/ DNUM = 2 \/ DNUM = 3 \/ DNUM = 4 \/ DNUM = 5 \/ DNUM = 6 \/ DNUM = 7)%Z.
Proof.
  pose proof dnum_range.
  mauto.
Qed.

Lemma HEAP_MAX_LENGTH_range: 
(0 <= HEAP_MAX_LENGTH<= Int.max_unsigned)%Z.
Proof.
unfold HEAP_MAX_LENGTH,IPC_STEP ,Int.max_unsigned, Int.modulus, Int.wordsize,Wordsize_32.wordsize . mauto.
Qed.

Lemma In_heap_NoDup_le : forall n m l vl h1 h2,
 NoDup (map fst (map fst (h1 ++ (l, n , vl)::h2))) -> 
 In_heapl_addrval (h1 ++ (l, n , vl)::h2) l m -> 
 (m <= n)%nat.
Proof.
  unfold In_heapl_addrval;intros.
  do 2 destruct H0. destruct H0.
  apply in_app_or in H0.
  destruct H0.
  - apply in_map with (f:= fst) in H0.
    apply in_map with  (f:= fst) in H0.
    cbn [fst] in *.
    rewrite list_append_map in H.
    rewrite list_append_map in H.
    cbn [map fst] in H.
    apply NoDup_remove_2 in H.
    false. apply H.
    apply in_or_app. tauto.
  - apply in_inv in H0.
    destruct H0. 
    + inversion H0;subst. auto.
    + apply in_map with (f:= fst) in H0.
    apply in_map with  (f:= fst) in H0.
    cbn [fst] in *.
    rewrite list_append_map in H.
    rewrite list_append_map in H.
    cbn [map fst] in H.
    apply NoDup_remove_2 in H.
    false. apply H. 
    apply in_or_app. tauto.
Qed.


Lemma firstn_nth_val' : 
 forall n vl x,
  n < length vl ->
  nth_val' n vl = x ->
  exists vl', 
  rev (firstn (n + 1)%nat vl) = x :: vl'.
Proof.
 induction n;intros.
 - destruct vl;simpl in H.
    inversion H.
   simpl (0 + _).
   cbn [firstn nth_val' rev] in *.
   rewrite H0.
   simpl (nil ++ _).
   eexists. eauto.
 - destruct vl;simpl in H.
    inversion H.
   apply lt_S_n in H.
   simpl (S _ + _).
   cbn [firstn nth_val' rev] in *.
   specialize (IHn _ _ H H0).
   destruct IHn.
   rewrite H1.
   simpl ((_ :: _) ++ _ ).
   eexists;eauto.
Qed.


Lemma PhdrArray_same_length: forall  v1 v2 v3 v4,
  PhdrArray_Pure  v1 v2 v3 v4 ->
  length v2 = length v1 /\ length v3 = length v1 /\ length v4 = length v1.
Proof.
  intros. induction H; intros; simpl; try tauto; repeat split; try f_equal; try tauto.
Qed.

Lemma PhdrArray_fold:
  (fix PhdrArray
           (file p : addrval) (vll : list vallist)
           (filevll memvll dstvll : list (option vallist)) {struct vll} : asrt :=
           match vll with
           | nil =>
               match filevll with
               | nil =>
                   match memvll with
                   | nil => match dstvll with
                            | nil => Aemp
                            | _ :: _ => Afalse
                            end
                   | _ :: _ => Afalse
                   end
               | _ :: _ => Afalse
               end
           | vl :: vll' =>
               match filevll with
               | nil => Afalse
               | filevl :: filevll' =>
                   match memvll with
                   | nil => Afalse
                   | memvl :: memvll' =>
                       match dstvll with
                       | nil => Afalse
                       | dstvl :: dstvll' =>
                           Astruct p Elf32_Phdr vl **
                           [|struct_type_vallist_match Elf32_Phdr vl|] **
                           PhdrSingle file vl filevl memvl dstvl **
                           PhdrArray file (get_off_addr p ($ size_of_Elf32_Phdr)) vll'
                             filevll' memvll' dstvll'
                       end
                   end
               end
           end) = PhdrArray.
Proof. reflexivity. Qed.

Lemma val_inj_ptr_get_off_addr_eq: forall b o n,
  val_inj (Some (Vptr (b, o +ᵢ  n))) = Vptr (get_off_addr (b,o) n).
Proof. intros. reflexivity. Qed.

Lemma Int16_max_unsigned_65535: Int16.max_unsigned = 65535%Z.
Proof. reflexivity.  Qed.

Lemma Int_max_unsigned_4294967295: Int.max_unsigned = 4294967295%Z.
Proof. reflexivity. Qed. 

Lemma Int16_max_unsigned_le_Int_max_unsigned: (Int16.max_unsigned <= Int.max_unsigned)%Z.
Proof. cbv. intros. discriminate. Qed.

Lemma ift_zero_rule :  forall Spec sd  I r ri p e  s pa t,
  (p ==> Rv e @ Tint32 ==  Vint32 Int.zero) ->
  InfRules Spec  sd pa I r ri p (sifthen e s) p  t.
Proof.
  intros.
  apply ift_rule with (tp:=Tint32).
   + intros. exists (Vint32 Int.zero).   auto.
   + intros. inversion H0. easy.
   + eapply backward_rule1. apply sep_aconj_r_aistrue_to_astar with (t:=Tint32).  apply H.
     apply pure_split_rule. intros. destruct H0. congruence.
Qed.

Lemma ift_nonzero_rule :  forall Spec sd  I r ri p q e  s pa t,
  (p ==> EX v, (Rv e @ Tint32 ==  Vint32 v ** [| Int.eq v Int.zero = false|])) ->
  InfRules Spec  sd pa I r ri p s q  t ->
  InfRules Spec  sd pa I r ri p (sifthen e s) q t.
Proof.
  intros.
  apply ift_rule with (tp:=Tint32).
  + intros. apply H in H1. sep destruct H1. sep auto. 
  + intros. destruct H1.  inversion H2. 
    apply H in H1. sep destruct H1.
    sep split in H1. inversion H1. 
    destruct H3. destruct H6.
    rewrite H3 in H5. inverts H5. unfold istrue in H7.
    rewrite H4 in H7. congruence.
  + eapply backward_rule1 with p. 
    intros. destruct H1. easy.
    assumption.
Qed.

Lemma aconj_absorb_r_rule: forall Spec sd pa I r ri p1 p2 s q t,
  InfRules Spec sd pa I r ri p1 s q t ->
  InfRules Spec sd pa I r ri (p1//\\p2) s q t.
Proof.
  intros.
  eapply backward_rule1 with p1.
  intros.
  now destruct H0.
  assumption.
Qed.

Lemma aconj_absorb_l_rule: forall Spec sd pa I r ri p1 p2 s q t,
  InfRules Spec sd pa I r ri p2 s q t ->
  InfRules Spec sd pa I r ri (p1//\\p2) s q t.
Proof.
  intros.
  eapply backward_rule1 with p2.
  intros.
  now destruct H0.
  assumption.
Qed.

Theorem call_rule'_twop:
  forall (f : fid)
         Spec
         (I : Inv) (r : retasrt) (ri : asrt)
          (pre : fpre) 
         (post : fpost) (p1 p2 P: asrt) (el : exprlist) 
         (vl : vallist) (tp : type) 
         (tl : typelist) (logicl:list logicvar) sc li tid,
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> Rvl el @ tl == vl ->
    P ==> PRE  [pre, vl,logicl,tid] ** p1 ** p2 ->
    GoodFrm (p1 ** p2) ->
    EX v , POST [post, vl, v, logicl,tid] ==>
                            EX lg : list logicvar, p_local li tid lg ** Atrue ->
   PRE [pre, vl, logicl, tid] ==> EX lg : list logicvar, p_local li tid lg ** Atrue  ->
    tl_vl_match tl vl =true ->
    {|Spec , sc , li, I, r, ri|} |- tid
                           {{ P}}
                           scall f el
                           {{ EX v,  POST  [post, vl, v,logicl,tid] ** p1 ** p2 }}.
Proof.
  intros.
  pose proof call_rule'.
  eapply call_rule'; eauto. 
Qed.

Theorem calle_rule_lvar'_twop :
  forall (f : fid)  (x : var)
         Spec (I : Inv) 
         (r : retasrt) (ri : asrt) 
         (pre : fpre) (post : fpost) 
         (p1 p2 P : asrt) (el : exprlist) (v' : val) 
         (vl : vallist)  (tp : type) 
         (tl : typelist) logicl sc li tid,
    Spec f = Some (pre, post, (tp, tl)) ->
    P ==> Rvl el @ tl == vl ->
    P ==> PRE  [pre, vl, logicl,tid] ** LV x @ tp |-> v' ** p1 ** p2 ->
    GoodFrm (p1 ** p2) ->
    retpost post ->
    tl_vl_match tl vl =true ->
    ( EX v : option val, POST [post, vl, v, logicl, tid]   ==> EX lg, p_local li tid lg ** Atrue) ->
    PRE [pre, vl, logicl, tid] ==> EX lg : list logicvar, p_local li tid lg ** Atrue  ->
    {|Spec , sc, li, I, r, ri|} |- tid
                           {{  P }}
                           scalle (evar x) f el
                           {{EX v,  POST  [post, vl, Some v,logicl,tid] ** LV x @ tp |-> v ** p1 ** p2}}.
Proof.
  intros.
  pose proof calle_rule_lvar'.
  eapply calle_rule_lvar'; eauto.
Qed.