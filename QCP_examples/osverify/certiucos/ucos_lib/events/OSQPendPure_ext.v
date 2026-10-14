
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.

Require Import q_common.
Require Import OSQPendPure.
Require Import OSQPostPure.
(* Require Import OS_EventTaskPostRdy_pure. *)
Require Import tcblist_setnode_lemmas.
Require Import OSTimeDlyPure.
Require Import OSTimeTickPure.
(* Require Import err_list_common. *)
Require Import sempend_pure_ext.
Require Import Mbox_common.
Require Import Lia.

(* Ltac sep_lift_absdata' H :=
  match type of H with
    | _ |= ?P =>
      match find_aop P with
        | none _ =>
          idtac 1 "no absop in the pre-condition"; fail 1
        | some ?a =>
          match find_absdata P absecblsid with
            | none _ =>
              idtac 2 "no HECBList in the pre-condition";
                fail 2
            | some ?b =>
              match find_absdata P abstcblsid with
                | none _ => 
                  idtac 3 "no HTCBList in the pre-condition"; fail 3
                | some ?c =>
                  match find_absdata P ostmid with
                    | none _ =>
                      idtac 4 "no HTime in the pre-condition"; fail 4
                    | some ?e =>
                      match find_absdata P curtid with
                        | none _ =>
                          idtac 5 "no HCurTCB in the pre-condition"; fail 5
                        | some ?f =>
                          sep lifts (a::b::c::e::f::nil)  in H
                      end
                  end
              end
          end
      end
    end. *)

Lemma msgqlist_p_compose_pend:
  forall  p qid mqls qptrl1 qptrl2 i i1 a x3 p' v'41 v'100
          msgqls1 msgqls2 msgq mqls1 mqls2 mq mqls' tcbls i2 x4,
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i2 :: x4 :: nil, v'41, v'100) tcbls ->
    R_ECB_PETbl_P qid
  (V$ OS_EVENT_TYPE_Q :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i2 :: x4 :: nil, v'41, v'100)
  tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls'->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (qptrl1 ++ ((V$OS_EVENT_TYPE_Q
                                    :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i2 :: x4 :: nil, v'41, v'100)::nil) ++ qptrl2) (msgqls1 ++ (msgq::nil) ++msgqls2) mqls tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

Lemma msgqnode_p_hold_end:
  forall b sti qens outi qend qptr qst qin qsize qblk  mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    Int.ltu ($ 0) qens =true ->
    qend = Vptr (b, (outi +ᵢ  Int.mul ($ 1) ($ 4))) -> 
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize nil , wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize nil, wl).
Proof.
  introv Hid Hint Hqend Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6). (* change by yss *) 
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i.
  inverts Hid.
  remember ( i1+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i0.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4)%Z.
  clear -i0.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0)%Z.
  clear.
  int auto.
  int auto.
  rewrite Zdiv_0_l.
  lia.
  simpl.
  rewrite Zdiv_0_l.
  lia.
  rewrite H5 in *.
  clear H5.
  splits.
  splits.
  introv Hlt.
  lets Hed :  math_le_xyz H1 H  H23; eauto. (* H22 -> H23 *)
  rewrite Int.repr_unsigned; eauto.    
  destruct Hed as   (Has & Hass & Hsd) .
  apply z_split in Has.
  destruct Has as [Has1 | Has2].
  lets Hef : int_ltu_eq_false Hint.
  apply H16 in Has1. (* H15 -> H16 *)
  destruct Has1.
  rewrite Hef in H5.
  destruct H5; tryfalse.
  destruct H5 as (Hs1 & Hs2).
  rewrite <- Hass in Hs2.
 
  remember ( ∘(Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)))) as N.
  remember (∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))))  as M.
   destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite vallist_seg_Sn in Hs2.
  simpl in Hs2.
  inverts Hs2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite <- Hsd in Hlss.
  auto.
  clear -N.
  mauto.
  apply H15 in Has2. (* H14 -> H15 *)
  rewrite <- Hass in Has2.
  rewrite vallist_seg_Sn in Has2.
  simpl in Has2.
  inverts Has2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite Hsd .
   destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  auto.
  clear -l.
  mauto.
  introv Hf.
  assert ( 0 <= Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) )%Z.
  apply Int.unsigned_range.
  false.
  lia.
  introv Hf.
  lets Hed :  math_le_xyz H1 H  H23; eauto. (* H22 -> H23 *)
  rewrite Int.repr_unsigned; auto.
  rewrite Hf in *.
  assert (0<=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Has.
  apply Int.unsigned_range.
  assert (0<Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          0=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Hc.
  lia.
  destruct Hc as [Hc1 | Hc2].
  apply H15 in Hc1. (* H14 -> H15 *)
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in Hc1.
  rewrite vallist_seg_Sn in Hc1.
  simpl in Hc1.
  inverts Hc1.
  left.
  splits; auto.
  simpl in H0.
  clear - H0.
  mauto.
  destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  apply H16 in Hc2. (* H15 -> H16 *)
  left.
  destruct Hc2.
  destruct H5.
  inverts H8.
  destruct H5.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in H8.
  rewrite vallist_seg_Sn in H8.
  simpl in H8.
  inverts H8.
  simpl in H0.
  split; auto.
  clear - H0.
  mauto.
  destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  destruct H14. (* H13 -> H14 *)
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; auto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf. tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
  (* 处理新增等待发送列表相关*)
  intros.
  auto.
  introv Hf.
  tryfalse.
Qed.

Lemma msgqnode_p_hold_no_end: 
  forall b sti qens outi qend qptr qst qin qsize qblk mblk ml hml hsize wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    length ml = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize nil, wl) ->
    RLH_ECBData_P 
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens  -ᵢ  $ 1) :: Vptr qblk :: nil)
             mblk ml ) (absmsgq hml hsize nil, wl).
Proof.
  introv Hid  Hlen Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6).
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i0.
  inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  splits.
  splits.
  introv Hlt.

  lets Hed :  math_xyz_prop2'  H1 H  Hlt; eauto.
  destruct Hed as   (Has & Hass & Hsd) .
  lets Hls : H11 Has. (* H12 -> H11 *)
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite  <- Hsd in Hls.
  rewrite <- Hass .
  eapply  vallistseg_n_m_split; eauto.
  unfold nat_of_Z.
  apply le_change.
  eapply Z2Nat.inj_le; try lia;try apply Int.unsigned_range.
  destruct H14. (* H13 -> H14 *)
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H13. (* H11 -> H13 *)
  unfold Pos.to_nat.
  simpl.
  eapply math_le_trans; eauto.
  introv Hf.
  lets Heas :math_xyz_prop3' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  destruct Hdisj as [Hd1 | Hd2].
  lets Hls : H15 Hd1. (* H14 -> H15 *)
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  lets Hrs : H16 Hd2. (* H15 -> H16 *)
  destruct Hrs.
  destruct H5 as (Hf1 & Hf2).
  inverts Hf2.
  destruct H5 as (Hf1 & Hf2).
  rewrite Hd2 in *.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  introv Hf.
  lets Heas :math_xyz_prop4' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite Hf.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  lets Hres : H11 Hdisj. (* H12 -> H11 *)
  rewrite Hf in Hres.
  rewrite <- Hseq in Hres.
  rewrite vallist_seg_Sn in Hres.
  inverts Hres.
  left.
  simpl in H0.
  splits; auto.
  clear - H0.
  mauto.
  rewrite Hseq.
  rewrite <- Hf.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H13. (* H11 -> H13 *)
  unfold Pos.to_nat.
  simpl.
  eapply  math_le_trans; eauto.
  destruct H14; auto. (* H13 -> H14 *)
  unfolds.
  eexists.
  splits.
  unfolds; simpl;  eauto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
  intros.
  eapply Hm3.
  introv Hf; tryfalse.
  intros.
  apply Hecb in H5.
  tryfalse.
  intro. auto.
  intro. tryfalse.
Qed.

(* Open Scope int_scope. *)

Lemma Astruct'_fold:
  forall s P  b  v  v'2,
s |= (PV (b, Int.zero) @ char_t |-> v **
   match v'2 with
   | nil => Afalse
   | v0 :: vl' =>
       PV (b,
          Int.zero +ᵢ
          $
          Z.of_nat
            (typelen char_t)) @
       STRUCT ev_aux_code.gjb_err_blk
       ⋆ |-> v0 **
       match vl' with
       | nil => Aemp
       | _ :: _ => Afalse
       end
   end)
**
 P->
    s |=   Astruct' (b , Int.zero)
    ⌞ ev_aux_code.errval @ char_t;
    ev_aux_code.nexteblk @
    STRUCT ev_aux_code.gjb_err_blk ⋆ ⌟
    (v ::v'2) ** P.
  intros.
  unfold Astruct'.
  sep pauto.
Qed.

Lemma Astruct_fold:
  forall s P v'3 v'37 v'32,
  Vptr v'3 = Vptr (v'37, Int.zero) ->
  struct_type_vallist_match
      ev_aux_code.gjb_err_blk_t v'32 ->
s |=match ev_aux_code.gjb_err_blk_t with
  | STRUCT _ ­{ dls }­ =>
      Astruct' (v'37, Int.zero) dls
        v'32
  | _ => Afalse
  end
**
 P->
    s |=    Astruct (v'37, Int.zero)
    ev_aux_code.gjb_err_blk_t v'32 ** P.
  intros.
  unfold Astruct.
  sep pauto.
Qed.

Lemma Astruct'_fold_event:
  forall s P v'40 l',
  s |= (match OS_EVENT with
         | STRUCT _ ­{ dls }­ =>
             (fix Astruct' (l : addrval) (dls0 : decllist) (vl : list val) {struct dls0} : asrt :=
                match vl with
                | nil => match dls0 with
                         | ⌞ ⌟ => Aemp
                         | dcons _ _ _ => Afalse
                         end
                | v :: vl' =>
                    match dls0 with
                    | ⌞ ⌟ => Afalse
                    | dcons _ (Tnull as t) dls' | dcons _ (Void as t) dls' |
                      dcons _ (char_t as t) dls' | dcons _ (Int16u as t) dls' |
                      dcons _ (long as t) dls' | dcons _ (_ ∗ as t) dls' =>
                        let (b, i) := l in
                        PV l @ t |-> v ** Astruct' (b, i +ᵢ  $ Z.of_nat (typelen t)) dls' vl'
                    | dcons _ (STRUCT _ ⋆ as t) dls' =>
                        let (b, i0) := l in
                        PV l @ t |-> v ** Astruct' (b, i0 +ᵢ  $ Z.of_nat (typelen t)) dls' vl'
                    | dcons _ (Tarray _ _ as t) dls' =>
                        let (b, i) := l in Astruct' (b, i +ᵢ  $ Z.of_nat (typelen t)) dls' vl'
                    | dcons _ (STRUCT _ ­{ _ }­ as t) dls' =>
                        let (b, i0) := l in Astruct' (b, i0 +ᵢ  $ Z.of_nat (typelen t)) dls' vl'
                    | _ => Afalse
                    end
                end) (v'40, Int.zero) dls
               l'
         | _ => Afalse
         end
  ** P )->
  s |=match OS_EVENT with
  | STRUCT _ ­{ dls }­ =>
      Astruct' (v'40, Int.zero) dls
        l'
  | _ => Afalse
  end ** P.
Proof.
  intros.
  unfold Astruct'.
  sep pauto.
Qed.

Lemma Astruct_fold_event:
  forall s P v'37 v'32,
s |=match OS_EVENT with
  | STRUCT _ ­{ dls }­ =>
      Astruct' (v'37, Int.zero) dls
        v'32
  | _ => Afalse
  end
**
 P->
    s |=    Astruct (v'37, Int.zero)
    OS_EVENT v'32 ** P.
  intros.
  unfold Astruct.
  sep pauto.
Qed. 

(* same in sempost_pure.v *)
Lemma node_fold':
  forall s P vl t b,
    s |= Astruct (b, Int.zero) t vl ** P ->
    struct_type_vallist_match t vl ->
    s |= node (Vptr (b, Int.zero)) vl t ** P.
  intros.
  unfold node.
  sep pauto.
Qed. 
(* end *)

(* Ltac mytac_lift_abserr :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P eblsid with
            | none _ => idtac 1 "no absebls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end. *)

(* Local Open Scope code_scope. *)

(* same in OSMutexPendPure1.v *)
Lemma dllseg_compose:
  forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
         (l1 l2 : list vallist),
    s |= dllseg h hp t1 tn1 l1 OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** dllseg tn1 t1 t2 tn2 l2  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl)** P ->
    s |= dllseg h hp t2 tn2 (l1 ++ l2)  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
  intros.
  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.

  apply astar_r_aemp_elim.
  eapply IHl1.
  sep auto.
  auto.
Qed.
(* end same *)

Lemma dllseg_to_tcbdllseg :
  forall l head headprev tail tailnext P s,
    s |=   dllseg  head headprev tail tailnext l OS_TCB_flag  V_OSTCBPrev V_OSTCBNext ** P -> s |= tcbdllseg head headprev tail tailnext l ** P.
    
Proof.
  intros.
  unfold tcbdllseg.
  eapply H.
Qed.

Lemma dllseg_Astruct_dllseg_compose :
  forall s v'43 v'5 x10 x9 i10 i9 i8 i7 i6 i5 i4 v'44 v'19 v'12 v'15,
  forall v'17 P,
  s |= Astruct (v'44, Int.zero) OS_TCB_flag
           (v'43
            :: v'5
               :: x10
                  :: x9
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) **
         dllseg v'43 (Vptr (v'44, Int.zero)) v'12 Vnull v'19 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
         dllseg v'15 Vnull v'5 (Vptr (v'44, Int.zero)) v'17 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P ->
  struct_type_vallist_match OS_TCB_flag
  (v'43
   :: v'5
      :: x10
         :: x9
            :: Vint32 i10
               :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) ->
  s |= tcbdllseg v'15 Vnull v'12 Vnull (v'17 ++((v'43
       :: v'5
          :: x10
             :: x9
                :: Vint32 i10
                   :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil)
      :: v'19)) ** P.
Proof.
   intros.
   unfold tcbdllseg.
   unfold V_OSTCBPrev.
   unfold V_OSTCBNext.
   eapply dllseg_compose.
   sep cancel (dllseg v'15).
   unfold dllseg. 
   sep auto.
   unfold node.
   sep auto.
   split; eauto.
Qed.

Lemma dllseg_Astruct_compose :
  forall s v'43 v'5 x10 x9 i10 i9 i8 i7 i6 i5 i4 v'44 v'19 v'12 ,
  forall  P,
  s |= Astruct (v'44, Int.zero) OS_TCB_flag
           (v'43
            :: v'5
               :: x10
                  :: x9
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) **
         dllseg v'43 (Vptr (v'44, Int.zero)) v'12 Vnull v'19 OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P ->
  struct_type_vallist_match OS_TCB_flag
  (v'43
   :: v'5
      :: x10
         :: x9
            :: Vint32 i10
               :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil) ->
s
|= dllseg (Vptr (v'44, Int.zero)) v'5 v'12 Vnull
     ((v'43
       :: v'5
          :: x10
             :: x9
                :: Vint32 i10
                   :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: nil)
      :: v'19) OS_TCB_flag (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
   intros.
   unfold dllseg. 
   sep auto.
   unfold node.
   sep auto.
   split; eauto.
Qed.

Lemma pend_expwt_pre:
  forall v'36 v'14 v'13 v'12 v'32 v'15 v'24 v'35 v'0 v'8 v'9 v'11 x x0 x1 pwl
             v'6 v'10 v'38 v'69 v'39 v'58 a b c v'62 v'7 v'100 v'101 vhold sus,
    v'100 <> Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'14 (Vint32 v'100) ->
    R_ECB_PETbl_P (v'32, Int.zero)
                ( (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 v'100 :: v'101 :: nil,
                  v'13),v'14) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq x x0 pwl, x1) v'6 v'10 ->
    Int.unsigned v'100 <= 255 ->
    array_type_vallist_match Int8u v'14 ->
    length v'14 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'100)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'14 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    TcbJoin (v'58, Int.zero) (a,b,c, sus) v'62 v'7 ->
    pwl<>nil /\ GetHWait v'7 pwl (v'58,Int.zero) /\ TcbMod.get v'7 (v'58,Int.zero) = Some (a,b,c, sus).
Proof.
  intros.
  lets Hs : tcbjoin_get_a H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by lia.
  assert (Int.unsigned v'39 < 8) as Hy by lia.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & sus' & Hst).
  intro; tryfalse.

  unfold get in Hst; simpl in Hst.
  rewrite Hs in Hst.
  inverts Hst.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'14)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'100 = Vint32 v'100) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'14).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
(*   destruct H2 as (H2&Hres). *)
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & sus0 & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
  unfold get in Hge; simpl in Hge.
  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3&Hres').
  destruct H3 as (Heg1 & Heg3 & Heg2 & Heg4).

  lets Hrgs : Heg4 Hs.
  
  destruct Hrgs as (xz & y & pqw & qw & Hem & Hin).
  unfold get in Hem; simpl in Hem.
  rewrite Hg in Hem.
  inverts Hem.
  assert (pqw = nil \/ pqw <> nil) by tauto.
  destruct H3.
  subst pqw.
  simpl in Hin; tryfalse.
  splits; auto.
  unfolds.
  splits; auto.
  do 4 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmsgq xz y pqw, qw) /\ In t' pqw) .
  splits; auto.
  lets Habs : Heg3 H22.
  destruct Habs as (prio' & m' & n' & sus' & Hbs).
  do 4 eexists; splits; eauto.
(*   destruct H17 as (H17&Hres''). *)
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try lia;
    eauto.
  assert (Vint32 v'100 = Vint32 v'100) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  lia.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
         Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  lia.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.

(* same in oscore_common.v *)
Lemma nth_val'2nth_val':
  forall (rtbl : list val) (n : nat) x,
    nth_val' n rtbl = Vptr x -> nth_val n rtbl = Some (Vptr x).
Proof.
  inductions rtbl;intros;simpl in *.
  destruct n;simpl in H;tryfalse.
  destruct n.
  simpl in H.
  subst;auto.
  simpl in H.
  eapply IHrtbl;eauto.
Qed.

(* same in OSEventTaskRdyPure.v *)
Lemma z_le_n_lt':
  forall x1,
    Int.unsigned x1 <= 7 ->
    (Z.to_nat (Int.unsigned x1) < ∘OS_EVENT_TBL_SIZE)%nat.
Proof.
  introv Hx.
  mauto.
Qed.

Lemma msgqlist_p_compose2:
  forall  p qid mqls qptrl1 qptrl2 i i1 a x3 p' v'41 v'42
          msgqls1 msgqls2 msgq mqls1 mqls2 mq mqls' tcbls i0 x6,(*add i0 x6*)
    R_ECB_ETbl_P qid
                 ((V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i0 :: x6 :: nil, v'41),v'42) tcbls ->
    R_ECB_PETbl_P qid
                 ((V$OS_EVENT_TYPE_Q
                   :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i0 :: x6 :: nil, v'41),v'42) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls'->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (qptrl1 ++ (((V$OS_EVENT_TYPE_Q
                                    :: Vint32 i :: Vint32 i1 :: Vptr a :: x3 :: p' :: Vint32 i0 :: x6 :: nil, v'41),v'42)::nil) ++ qptrl2) (msgqls1 ++ (msgq::nil) ++msgqls2) mqls tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

(* same in OSQDel_proof.v *)
Lemma ECBList_P_Set_Post_Rdy_hold:
  forall a tcbls tid prio  msg msg'  x y  b c eid nl sus sus',
    TcbMod.get tcbls tid =  Some (prio, wait (os_stat_postq eid) nl, msg, sus) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio,rdy,msg', sus')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  simpljoin1.
  rename H3 into H2'.
  rename H4 into H3.
  destruct b; tryfalse.
  destruct a.
  destruct p.
  simpljoin1.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  simpljoin1.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H12.
  apply H12 in H13.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in H13; simpl in H13.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  apply H8 in H12.
  apply H12 in H13.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in H13; simpl in H13.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H9 in H12.
  apply H12 in H13.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in H13; simpl in H13.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  apply H10 in H12.
  apply H12 in H13.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in H13; simpl in H13.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  apply H11 in H12.
  apply H12 in H13.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H14.
  subst tid.
  unfold get in H13; simpl in H13.
  rewrite H13 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 sus0 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H12.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H12.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H12.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H12.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.
  
  destruct H12.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H11; eauto.

  simpljoin1;auto.

  unfolds.
  unfolds in H2'.
  
  split.
  destructs H2'.
  unfolds;intros.
 
  apply H6 in H8.
  apply H8 in H9.
  simpljoin1.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H10.
  subst tid.
  unfold get in H9; simpl in H9.
  rewrite H9 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  destructs H2'.
  intros prio' mg ng x3 sus0 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H8.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H7; eauto.
  
  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.

Lemma msgqnode_p_hold_end_part:
  forall b sti qens outi qend qptr qst qin qsize qblk  mblk ml hml hsize pwl wl l,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    Int.ltu ($ 0) qens =true ->
    qend = Vptr (b, (outi +ᵢ  Int.mul ($ 1) ($ 4))) -> 
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize pwl , wl) ->
      (MatchLHMsgList (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil) ml hml) /\
     (MatchLHMsgLength (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)  hml) /\
     (MatchLHMsgSize (qptr
                :: qst
                :: qend
                :: qin
                :: qst
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil) (Int.unsigned hsize)).
Proof.
  introv Hid Hint Hqend Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6). (* change by yss *) 
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i.
  inverts Hid.
  remember ( i1+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i0.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4)%Z.
  clear -i0.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0)%Z.
  clear.
  int auto.
  int auto.
  rewrite Zdiv_0_l.
  lia.
  simpl.
  rewrite Zdiv_0_l.
  lia.
  rewrite H5 in *.
  clear H5.
  splits.
  splits.
  introv Hlt.
  lets Hed :  math_le_xyz H1 H  H23; eauto. (* H22 -> H23 *)
  rewrite Int.repr_unsigned; eauto.    
  destruct Hed as   (Has & Hass & Hsd) .
  apply z_split in Has.
  destruct Has as [Has1 | Has2].
  lets Hef : int_ltu_eq_false Hint.
  apply H16 in Has1. (* H15 -> H16 *)
  destruct Has1.
  rewrite Hef in H5.
  destruct H5; tryfalse.
  destruct H5 as (Hs1 & Hs2).
  rewrite <- Hass in Hs2.
 
  remember ( ∘(Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)))) as N.
  remember (∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))))  as M.
   destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite vallist_seg_Sn in Hs2.
  simpl in Hs2.
  inverts Hs2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite <- Hsd in Hlss.
  auto.
  clear -N.
  mauto.
  apply H15 in Has2. (* H14 -> H15 *)
  rewrite <- Hass in Has2.
  rewrite vallist_seg_Sn in Has2.
  simpl in Has2.
  inverts Has2; auto.
  rewrite Int.unsigned_repr in Hsd.
  rewrite Hsd .
   destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  auto.
  clear -l.
  mauto.
  introv Hf.
  assert ( 0 <= Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) )%Z.
  apply Int.unsigned_range.
  false.
  lia.
  introv Hf.
  lets Hed :  math_le_xyz H1 H  H23; eauto. (* H22 -> H23 *)
  rewrite Int.repr_unsigned; auto.
  rewrite Hf in *.
  assert (0<=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Has.
  apply Int.unsigned_range.
  assert (0<Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          0=Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) )%Z as Hc.
  lia.
  destruct Hc as [Hc1 | Hc2].
  apply H15 in Hc1. (* H14 -> H15 *)
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in Hc1.
  rewrite vallist_seg_Sn in Hc1.
  simpl in Hc1.
  inverts Hc1.
  left.
  splits; auto.
  simpl in H0.
  clear - H0.
  mauto.
  destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  apply H16 in Hc2. (* H15 -> H16 *)
  left.
  destruct Hc2.
  destruct H5.
  inverts H8.
  destruct H5.
  destruct Hed as (He1 & He2 & He3).
  rewrite vallist_seg_eqnil in *.
  rewrite <- He2 in H8.
  rewrite vallist_seg_Sn in H8.
  simpl in H8.
  inverts H8.
  simpl in H0.
  split; auto.
  clear - H0.
  mauto.
  destruct H14 as (His & Hsi). (* H13 -> H14 *)
  lets Hlss : isptr_length_nth His.
  rewrite He3.
  rewrite Int.unsigned_repr.
  auto.
  clear -l.
  mauto.
  destruct H14. (* H13 -> H14 *)
  auto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; auto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
Qed.

Lemma ecblist_p_post_exwt_hold1_end':
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 (v'35:val) v'16
           v'19  v'21 v'22 v'23 v'25 v'26  x0 pwl x1 (v'0:val) v'1
          v'5 v'6 v'7 v'00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st (msg1:msg) y vhold v'86 v'82 x1' x0'
          pgrep petbl v100 (* x' *) msg2 x msg sus sus',
    pgrep <> Int.zero ->
    Int.unsigned pgrep <= 255 ->
    array_type_vallist_match char_t petbl ->
    length petbl = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned pgrep)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) petbl = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P petbl (Vint32 pgrep) ->
(**)    
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 pgrep :: v100 :: nil,
                  v'13 , petbl) v'7 ->
     R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32  pgrep :: v100 :: nil,
                  v'13, petbl) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: Vptr (v'23, $ 4)
                :: v'19
                :: Vptr (v'23, v'82)
                :: Vptr (v'23, x1')
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'86 ) (absmsgq (msg1::x) x0 pwl, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq (msg1::x) x0 pwl, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    pwl <> nil ->
    (MatchLHMsgList
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (update_nth_val
            (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
            v'86 x0') (x ++ msg2 :: nil) /\
       MatchLHMsgLength
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (x ++ msg2 :: nil) /\
       MatchLHMsgSize
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (Int.unsigned x0)) ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    (V$OS_EVENT_TYPE_Q
                       :: Vint32 v'12
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0  :: Vint32 y :: v100 :: nil, v'13 ,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: Vptr (v'23, $ 4)
                              :: v'19
                              :: Vptr (v'23, $ 4)
                              :: Vptr (v'23, $ 4)
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) (update_nth_val
         (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v'86 x0')
) :: v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq (x++msg2::nil) x0 (remove_tid (v'58, Int.zero) pwl), x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , v'00, sus'))
.
Proof.
  intros.
  rename H23 into Hrlh. 
  rename H14 into H13'. rename H15 into H14; rename H16 into H15; rename H17 into H16; rename H18 into H17;
  rename H19 into H18; rename H20 into H19; rename H21 into H20; rename H22 into H21.
  unfolds in H20.
  destruct H20 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H4 H8.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H9.
  lets Hps : Ha1 H20 H9.
  apply tcbjoin_get_a in H19.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H19.
  destruct H19;auto.
  destruct Hps as (sts & mg & sus0 & Hget);auto.
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H19.
  inverts H19.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H13.
  destruct H13 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha'''&Ha''''').
  destruct Hb as (Hb&Hb'&Hb''&Hb'''&Hb''''').
  destruct H13' as (Hd & He).
  lets Hz : math_unmap_get_y H0 H3.
  lets Heq1 :  math_mapval_core_prop H10; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H8.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H8.
  mauto.
  rewrite H13 in H5.
  assert (PrioWaitInQ (Int.unsigned prio) petbl) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H19.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H.
  rewrite <-H13 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H0 H  H3 H5 H12.
  lia.
  auto.
  lets Hecp : Hd Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hecp in H22.
  clear Hecp.
  rename H22 into Hecp.
  destruct Hecp as (ct & nl & mg & sus0 & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H22; auto.
  lets Heqs : Ha3 H22 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmsgq (x ++ msg2 :: nil) x0 (remove_tid tid pwl), x1)  H17  H18.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  change ((v'30 ++
   (V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))) :: v'1)) with ((v'30 ++
   ((V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))):: nil) ++ v'1)).
  change ((v'31 ++
   DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: v'5)) with ((v'31 ++
   (DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: nil)++ v'5)).
   
  eapply msgqlist_p_compose2.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rename Hprs1 into Hpq.
  rename Hprs2 into Hneq.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.
  
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.

  unfolds.
  splits;
  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  simpl fst in Hc;simpl;auto.
  
  unfolds.
  splits.
  unfolds.
  unfold R_ECB_PETbl_P in Hd. 
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).

  rewrite H13 in Hprs1.
  rewrite H19 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Hd.
  lets Hxs : Hd Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.


  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in He.
  lets Hga : He Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') petbl /\ prio' <> prio) .
  splits; auto.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H24.
  rewrite H19.
  rewrite H13.
  auto.

  instantiate (1:=v'9).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H14.
  revert Heqtid.
  simpljoin1.
  intros.
  unfolds in r.
  apply r in H21.
(*   subst x. *)
  instantiate (1:=(absmsgq (x ++ msg2 :: nil) x0  (remove_tid tid pwl), x1)).
  2: eapply Hsj1.
  2:eapply Hsj2.
  splits; auto.

(*   destruct r as (r1 & r2 &r3 & r4).
  destruct Hrlh as (t1 & t2 & t3).
  eauto.
   destruct Hrlh as (t1 & t2 & t3).
  eauto. *)
  
  unfolds.
  destruct r as (r1 & r2 &r3 & r4).
  splits. intros; auto; tryfalse. intros. auto.
  intros.
  assert( (msg1::x) = nil -> ((x ++ msg2 :: nil) = nil) ).
  {
    intros.
    destruct x;
    tryfalse.
  }
   eapply H20.
  eapply r2. auto.
  clear -r1 r2 r3 r4.
  intros.
  assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0 in H.
   apply r3 in H.
   rewrite H.
   simpl. auto.
   
   clear -r1 r2 r3 r4.
   intros.
   assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0.
   eapply r4.
   destruct pwl.
   simpl in H; tryfalse.
   auto.
Qed.

Lemma isptr_list_tail_add':
  forall x1 x0,
    isptr x0 ->
    isptr_list x1 ->
    isptr_list (x1 ++ x0 :: nil).
Proof.
  introv H0.
  inductions x1.
  simpl.
  intros; splits; auto.
(*   unfolds.
  right; eauto. *)
  intros.
  simpl in H.
  destruct H as (His & Hip).
  apply IHx1 with x0 in Hip.
  simpl.
  split; auto.
  auto.
Qed.

Lemma rlh_ecbdata_in_end_part:
  forall i1 i2 x13 x12 v'49 x x8 v'86 x4 x6 x0,
    Int.ltu i1 i2 = true ->
    length v'86 = ∘OS_MAX_Q_SIZE ->
    isptr x0 ->
    WellformedOSQ
      (x13
         :: x12
         :: Vptr (v'49, (x+ᵢInt.mul ($ 1) ($ 4)) )
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
      MatchLHMsgList
        (x13
         :: x12
            :: Vptr (v'49, x +ᵢ  Int.mul ($ 1) ($ 4))
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1:: Vptr (v'49, Int.zero) :: nil) v'86
        x4 /\
      MatchLHMsgLength
        (x13
         :: x12
            :: Vptr (v'49, x +ᵢ  Int.mul ($ 1) ($ 4))
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) x4 /\
      MatchLHMsgSize
        (x13
         :: x12
            :: Vptr (v'49, x +ᵢ  Int.mul ($ 1) ($ 4))
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1:: Vptr (v'49, Int.zero) :: nil)
        (Int.unsigned x6) ->
        MatchLHMsgList
        (x13
                :: x12
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x12
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil) (update_nth_val
                 (Z.to_nat ((Int.unsigned x - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                 v'86 x0)
        (x4 ++ ( x0 :: nil)) /\
      MatchLHMsgLength
        (x13
                :: x12
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x12
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil) (x4 ++ ( x0 :: nil)) /\
      MatchLHMsgSize
        (x13
                :: x12
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x12
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil)
        (Int.unsigned x6).
Proof.
  introv Hi Hlen Hx0 Hw Hr.
  funfold Hw.
  rename x11 into qents; rename H15 into Hqensltsize; rename H16 into H15. (* new add *)
  unfold qend_right, arrayelem_addr_right in *.
  unfold ptr_offset_right,   ptr_minus  in *.
  fsimpl.
  simpl in H10.
  subst i0.
  simpl in H8.
  inverts H8.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -b0.
  mauto.
  rewrite H4 in *.
  simpl in H13, H15, H16.
  rename H0 into Hm1.
  rename H1 into Hm2.
  rename H2 into Hm3.
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  rewrite Int.repr_unsigned in *.
  lets Hcp : Hi.
  rewrite Intlt_true_is_Zlt in Hcp. 
  rewrite H1 in Hcp.
  assert (Hneq: length x4 <> Z.to_nat (Int.unsigned x6)).
  {
  eapply Z2Nat.id in H8.
  rewrite <- H8 in Hcp.
  rewrite <- Nat2Z.inj_lt in Hcp.
  pure_auto.
  rewrite <- H0 in Hcp.
  clear -Hcp.
  induction x4; simpl in *; auto with zarith.
  }
  simpl in H18 , H20 ,  H21.
  splits.
  unfolds.
  assert (Int.unsigned (Int.divu ($ 4-ᵢ$ 4) ($ 4)) = 0).
  clear -x.
  repeat progress (int auto);simpl;
  try    rewrite Zdiv_0_l;lia.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $ 4).
  clear -x.
  mauto.
  assert (Int.unsigned ($ 4) = 4).
  clear -x.
  int auto.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  rewrite H0 in *.
  clear H0.
  rewrite H2 in *.
  rewrite H12 in *.
  lets Heq : math_le_xyz  H15 H3 H14 H H6; eauto. (* H14,15 -> H15,14 *)
  rewrite Int.repr_unsigned; auto.
  rewrite H12 in *.
  destruct Heq as (Hle & Hse & He).    
  assert ( Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) >  Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4)) \/
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) =  Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))) by lia.
  destruct H0 as [Ha1 | Ha2].
  lets Hres : H18 Ha1.
  remember ( ∘(Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4)))) as M.
  remember (∘(Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)))) as N.
  rewrite  <- He.
  splits.
  splits.
  intros.
  assert (0<=Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))).
  apply Int.unsigned_range.
  lia.
  intros.
  rewrite <- Hse.
  lets Heqs : math_le_max_q H15 H5 Hse. (* H14 -> H15 *)
  destruct Heqs as (Hs1 & Hs2).
  lets Has : vallist_seg_upd_prop  (x0) Hres. 
  rewrite Hlen.
  auto.
  auto.
  rewrite Has.
  unfold vallist_seg.
  simpl.
  rewrite app_nil_r.
  auto.
  intros.
  right.
  lets Heqs : math_le_max_q H15 H5 Hse. (* H14 -> H15 *)
  destruct Heqs as (Hs1 & Hs2).
  lets Has : vallist_seg_upd_prop (x0) Hres. 
  rewrite Hlen.
  auto.
  auto.
  rewrite <- Hse.
  rewrite Has.
  lets Hcs : math_len_le_and (x0) Hlen H15 H5 Hse. (* H14 -> H15 *)
  destruct Hcs as (Hcs1 & Hcs2).
  split.
  lets Hsss : vallist_seg_length_prop Has.
  auto.
  auto.
  rewrite <- H0 in *.
  subst M.
  rewrite app_length in Hsss.
  simpl in Hsss.
  eapply math_length_int_eq; eauto.
  unfold vallist_seg.
  simpl.
  rewrite app_nil_r.
  auto.
  eapply isptr_list_tail_add';eauto.
  lets Heqs : H21 Ha2.
  rewrite <- He.
  rewrite Ha2.
  remember ( ∘(Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4)))) as M.
  splits.
  splits.
  assert (0<=Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))).
  apply Int.unsigned_range.
  intros.
  clear - H0 H17.
  lia.
  intros.  
  rewrite <- Hse.
  rewrite Ha2.
  rewrite <-HeqM.
  destruct Heqs.
  destruct H17.
  subst x4.
  simpl.
  rewrite  vallist_seg_upd_SM.
  unfold vallist_seg;simpl.
  auto.
  rewrite Hlen.
  eapply math_max_le_q; eauto.
  destruct H17.
  eapply ltu_eq_false in Hi.
  rewrite  Int.eq_sym in Hi.
  rewrite Hi in H17.
  inverts H17.
  introv Hz.
  rewrite <- Hz in *.
  right. 
  rewrite <- Hse.
  rewrite Ha2.
  rewrite HeqM.
  destruct Heqs.
  destruct H0.
  subst x4.
  rewrite  vallist_seg_upd_SM.
  unfold vallist_seg;simpl.
  splits.
  eapply math_length_int_eq; eauto.
  simpl.
  rewrite Ha2 in Hse.
  simpl in Hse.
  rewrite <- Hse.
  auto.
  auto.
  rewrite Hlen.
  simpl.
  unfold Pos.to_nat;simpl; lia.
  destruct H0 as (Hfs &_).
  eapply ltu_eq_false in Hi.
  rewrite Int.eq_sym in Hi.
  rewrite Hi in Hfs.
  inverts Hfs.
  eapply isptr_list_tail_add';eauto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; eauto.
  rewrite app_length.
  simpl.
  eapply  math_inc_eq_ltu; eauto.
  unfolds.
  eexists.
  splits; auto.
  unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
Qed.

Lemma rlh_ecbdata_in_noend_part:
  forall i1 i2 x13 x12 v'49 x x8  x0 x6 v'86 x4 x7,
    x6 <> Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4)) ->
    Int.ltu i1 i2 = true ->
    length v'86 = ∘OS_MAX_Q_SIZE ->
    isptr x0 ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
      MatchLHMsgList
        (x13
         :: x12
            :: x6
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1:: Vptr (v'49, Int.zero) :: nil) v'86
        x4 /\
      MatchLHMsgLength
        (x13
         :: x12
            :: x6
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) x4 /\
      MatchLHMsgSize
        (x13
         :: x12
            :: x6
               :: Vptr (v'49, x)
                  :: x8
                     :: Vint32 i2 :: Vint32 i1:: Vptr (v'49, Int.zero) :: nil)
        (Int.unsigned x7) ->
        MatchLHMsgList
        (x13
                :: x12
                :: x6
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil) (update_nth_val
                 (Z.to_nat ((Int.unsigned x - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
                 v'86 x0)
        (x4 ++ ( x0 :: nil)) /\
      MatchLHMsgLength
        (x13
                :: x12
                :: x6
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil) (x4 ++ ( x0 :: nil)) /\
      MatchLHMsgSize
        (x13
                :: x12
                :: x6
                :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
                :: x8
                :: Vint32 i2
                :: Vint32 (i1 +ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil)
        (Int.unsigned x7).
Proof.
  introv Hneq Hi Hlen Hx0 Hw Hr.
  funfold Hw.
  rename x14 into qents; rename H15 into Hqensltsize; rename H16 into H15. (* new add *)
  unfold qend_right, arrayelem_addr_right in *.
  unfold ptr_offset_right,   ptr_minus  in *.
  fsimpl.
  simpl in H10 ,H16,H15, H13, H8.
  inverts H8.
  assert (Int.mul ($ 1) ($ 4) = $ 4).

  mauto.
  rewrite H8 in *.
  assert (i1 <> x+ᵢ$ 4) as Hni. (* i2 -> i1 *)
  introv Hf.
  apply Hneq.
  subst i1. (* i2 -> i1 *)
  auto.
  clear Hneq.
  rename H0 into Hm1.
  rename H1 into Hm2.
  rename H2 into Hm3.

  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  rewrite Int.repr_unsigned in *.
  lets Hcp : Hi.
  rewrite Intlt_true_is_Zlt in Hcp.
  simpl in H19 , H21 ,  H22.
  remember (Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) as M.
  remember (Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))) as N.
  assert (Int.unsigned ($ 4) = 4).
  clear -x.
  int auto.
  rewrite H4 in *.
  rewrite H0 in *.
  splits.
  unfolds.
  do 7 eexists; splits; try solve [unfolds; simpl; eauto].
  splits.
  splits.
  introv Hc1.
  lets Heq :math_int_lt_eq_split H3 H HeqM HeqN  Hc1; eauto.
  destruct Heq as (He1 & He2 & He3 & He4).
  rewrite He3.
  rewrite He1.
  destruct He2 as [Hea1 | Hea2].
  lets Hca1 : H19 Hea1.
  lets Has : vallist_seg_upd_prop (x0) Hca1.
  rewrite Hlen.
  apply He4.
  apply He4.
  rewrite Has.
  auto.
  lets Hrs : H22 Hea2.
  destruct Hrs as [Hrs1 | Hrs2].
  destruct Hrs1 as (Heq1 & Heq2).
  subst x4.
  rewrite Hea2.
  rewrite  vallist_seg_upd_SM.
  simpl; auto.
  rewrite Hlen.
  rewrite <-Hea2.
  destruct He4.
  clear - H2.
  lia.
  destruct Hrs2 as (Hie & _).
  eapply ltu_eq_false in Hi.
  rewrite Int.eq_sym in Hi.
  rewrite Hi in Hie.
  tryfalse.
  introv Hc2.
  lets Heq :math_int_lt_eq_split' H3 H HeqM HeqN  Hc2; eauto.
  destruct Heq as (He1 & He2 & He3 & He4).
  rewrite He3.
  rewrite He1.
  lets Hres : H21 He2.
  rewrite vallist_seg_upd_irr with (y:= (x0)) (M:=∘M)in Hres;auto.
  remember ( vallist_seg 0 ∘M v'86) as xy.
  apply eq_sym in Heqxy.
  lets Has : vallist_seg_upd_prop (x0) Heqxy.
  rewrite Hlen.
  clear - He4.
  destruct He4.
  lia.
  clear -x.
  lia.
  rewrite Has.
  rewrite app_assoc.
  rewrite Hres.
  auto.
  apply He4.
  rewrite Hlen.
  apply He4.
  introv Hc3.
  lets Heq :math_int_lt_eq_split'' H3 H HeqM HeqN  Hc3; eauto.
  right.
  destruct Heq as (He1 & He2 & He3 & He4).
  destruct He2 as (Hes & Hek).
  rewrite He3.
  rewrite He1.
  lets Hrs : H21 Hek.
  rewrite vallist_seg_upd_irr with (y:= (x0)) (M:=∘M)in Hrs;auto.
  remember ( vallist_seg 0 ∘M v'86) as xy.
  apply eq_sym in Heqxy.
  lets Has : vallist_seg_upd_prop (x0) Heqxy.
  rewrite Hlen.
  clear - He4.
  simpljoin1.
  lia.
  clear -x.
  lia.
  rewrite Has.
  rewrite app_assoc.
  rewrite Hrs.
  remember ( vallist_seg ∘N ∘(Int.unsigned x7) (update_nth_val ∘M v'86 (x0))) as l1.
  remember (vallist_seg 0 (S ∘M) (update_nth_val ∘M v'86 (x0))) as l2.
  apply eq_sym in Heql1.
  apply eq_sym in Heql2.
  lets Hl1 : vallist_seg_length_prop Heql1.
  clear - H5.
  lia.
  rewrite update_nth_val_len_eq.
  rewrite Hlen.
  clear -He4.
  simpljoin1.
  lia.
  lets Hl2 : vallist_seg_length_prop Heql2.
  clear -x.
  lia.
  rewrite update_nth_val_len_eq.
  rewrite Hlen.
  clear -He4.
  simpljoin1.
  rewrite H0.
  lia.
  assert (length (l1 ++ xy) = length x4).
  rewrite Hrs; auto.
  assert (length l2 = length ( xy ++ x0 :: nil)) .
  rewrite Has.
  auto.
  rewrite app_length in H2.
  rewrite app_length in H17.
  rewrite Hl1 in H2.
  rewrite Hl2 in H17.
  simpl in H17.
  assert (length xy = ∘M)% nat.
  clear - H17.
  lia.
  rewrite H18 in H2.
  assert (length x4 =(∘(Int.unsigned x7)-1))%nat.
  clear - H2 He4 H5 H7.
  simpljoin1.
  rewrite <- H0 in H2.
  lia.
  split; auto.
  eapply math_int_eq_len; eauto.
  clear - He4.
  simpljoin1.
  lia.
  rewrite Hlen.
  eapply He4.
  eapply isptr_list_tail_add';eauto.
  unfolds.
  eexists.
  splits.
  unfolds; simpl; eauto.
  rewrite app_length.
  simpl.
  eapply  math_inc_eq_ltu; eauto.
  unfolds.
  eexists.
  splits; auto.
  unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
Qed.

Lemma ecblist_p_post_exwt_hold1_noend':
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 (v'35:val) v'16
           v'19  v'21 v'22 v'23 v'25 v'26  x0 pwl x1 (v'0:val) v'1
          v'5 v'6 v'7 v'00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st (msg1:msg) y vhold v'86 v'82 x1' x0'
          pgrep petbl v100 (* x' *) msg2 x msg sus sus',
    pgrep <> Int.zero ->
    Int.unsigned pgrep <= 255 ->
    array_type_vallist_match char_t petbl ->
    length petbl = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned pgrep)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) petbl = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P petbl (Vint32 pgrep) ->
(**)    
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 pgrep :: v100 :: nil,
                  v'13 , petbl) v'7 ->
     R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32  pgrep :: v100 :: nil,
                  v'13, petbl) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: Vptr (v'23, $ 4)
                :: v'19
                :: Vptr (v'23, v'82)
                :: Vptr (v'23, x1')
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'86 ) (absmsgq (msg1::x) x0 pwl, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq (msg1::x) x0 pwl, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    pwl <> nil ->
    (MatchLHMsgList
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (update_nth_val
            (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
            v'86 x0') (x ++ msg2 :: nil) /\
       MatchLHMsgLength
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (x ++ msg2 :: nil) /\
       MatchLHMsgSize
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, $ 4)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (Int.unsigned x0)) ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    (V$OS_EVENT_TYPE_Q
                       :: Vint32 v'12
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0  :: Vint32 y :: v100 :: nil, v'13 ,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: Vptr (v'23, $ 4)
                              :: v'19
                              :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                              :: Vptr (v'23, $ 4)
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) (update_nth_val
         (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v'86 x0')
) :: v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq (x++msg2::nil) x0 (remove_tid (v'58, Int.zero) pwl), x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , v'00, sus'))
.
Proof.
  intros.
  rename H23 into Hrlh. 
  rename H14 into H13'. rename H15 into H14; rename H16 into H15; rename H17 into H16; rename H18 into H17;
  rename H19 into H18; rename H20 into H19; rename H21 into H20; rename H22 into H21.
  unfolds in H20.
  destruct H20 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H4 H8.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H9.
  lets Hps : Ha1 H20 H9.
  apply tcbjoin_get_a in H19.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H19.
  destruct H19;auto.
  destruct Hps as (sts & mg & sus0 & Hget);auto.
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H19.
  inverts H19.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H13.
  destruct H13 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha'''&Ha'''').
  destruct Hb as (Hb&Hb'&Hb''&Hb'''&Hb'''').
  destruct H13' as (Hd & He).
  lets Hz : math_unmap_get_y H0 H3.
  lets Heq1 :  math_mapval_core_prop H10; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H8.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H8.
  mauto.
  rewrite H13 in H5.
  assert (PrioWaitInQ (Int.unsigned prio) petbl) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H19.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H.
  rewrite <-H13 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H0 H  H3 H5 H12.
  lia.
  auto.
  lets Hecp : Hd Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hecp in H22.
  clear Hecp.
  rename H22 into Hecp.
  destruct Hecp as (ct & nl & mg & sus0 & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H22; auto.
  lets Heqs : Ha3 H22 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmsgq (x ++ msg2 :: nil) x0 (remove_tid tid pwl), x1)  H17  H18.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  change ((v'30 ++
   (V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))) :: v'1)) with ((v'30 ++
   ((V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))):: nil) ++ v'1)).
  change ((v'31 ++
   DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: v'5)) with ((v'31 ++
   (DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: nil)++ v'5)).
   
  eapply msgqlist_p_compose2.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rename Hprs1 into Hpq.
  rename Hprs2 into Hneq.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.
  
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  
  unfolds.
  splits;
  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  simpl fst in Hc;simpl;auto.
  
  unfolds.
  splits.
  unfolds.
  unfold R_ECB_PETbl_P in Hd. 
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).

  rewrite H13 in Hprs1.
  rewrite H19 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Hd.
  lets Hxs : Hd Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.


  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in He.
  lets Hga : He Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') petbl /\ prio' <> prio) .
  splits; auto.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H24.
  rewrite H19.
  rewrite H13.
  auto.

  instantiate (1:=v'9).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H14.
  revert Heqtid.
  simpljoin1.
  intros.
  unfolds in r.
  apply r in H21.
(*   subst x. *)
  instantiate (1:=(absmsgq (x ++ msg2 :: nil) x0  (remove_tid tid pwl), x1)).
  2: eapply Hsj1.
  2:eapply Hsj2.
  splits; auto.

  unfolds.
  destruct r as (r1 & r2 &r3 & r4).
  splits. intros; auto; tryfalse. intros. auto.
  intros.
  assert( (msg1::x) = nil -> ((x ++ msg2 :: nil) = nil) ).
  {
    intros.
    destruct x;
    tryfalse.
  }
   eapply H20.
  eapply r2. auto.
  clear -r1 r2 r3 r4.
  intros.
  assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0 in H.
   apply r3 in H.
   rewrite H.
   simpl. auto.
   
   clear -r1 r2 r3 r4.
   intros.
   assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0.
   eapply r4.
   destruct pwl.
   simpl in H; tryfalse.
   auto.
Qed.

Lemma rh_tcblist_ecblist_p_pent_expwt:
  forall v'8 tid v'11 v'7 v'9 v'10 eid  x0 x1 v'6 prio  msg xl pwl x3 x4 x5 sus sus',
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmsgq (x3::x4) x0 pwl, x1) v'6 v'10 ->
    In tid pwl ->
    TcbMod.get v'7 tid = Some (prio,  wait (os_stat_postq eid) xl, msg, sus) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid
                  (absmsgq (x4 ++ x5 :: nil) x0 (remove_tid tid pwl), x1))
      (TcbMod.set v'7 tid
                  (prio, rdy , x5, sus')) v'8.
Proof.
  intros.
  unfolds.
  splits.
  splits. 
   (*slove goal1 with H'*)
  unfolds in H.
  destruct H as (H&Hx).
  destruct H as (H & H' & H6 & H6').
  intros.
  destruct H4.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  (*tid = tid0 *) 
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  
  assert (get (EcbMod.set v'11 eid (absmsgq  (x4 ++ x5 :: nil) x0 (remove_tid tid0 pwl),  x1)) eid = Some (absmsgq  (x4 ++ x5 :: nil) x0 (remove_tid tid0 pwl), x1) ).
  eapply map_tactics.get_set_eq.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  (* eid = eid0*)
  subst.
  unfold get in H4,H7;simpl in H4,H7.
  rewrite H4 in H7.
  assert (qwaitset = x1).
  inverts H7. auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq (x3 :: x4) x0 pwl, x1)/\ In tid0 x1 ).
  splits. auto. rewrite H8 in H5. auto.
  lets Hsa : H H9.
  simpljoin1.
  unfold get in H10; simpl in H10.
  rewrite H3 in H10.
  inverts H10.
   (* eid <> eid0*)
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid0 qwaitset ).
  splits;auto.
  lets Hsc : H H9.
  simpljoin1.
  unfold get in H10;simpl in H10.
  rewrite H3 in H10. inverts H10.
  (*tid <> tid0*)
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  lets Hbss :tidneq_inwt_in  qwaitset H7.
  destruct Hbss as (Hbss & _).
  (* lets Hbssc : Hbss H5. *)
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq (x3 :: x4) y pwl, qwaitset) /\ In tid0 qwaitset ).
  splits; auto.
  apply H in H4.
  simpljoin1.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq x y pqwaitset, qwaitset)/\ In tid0 qwaitset ).
  splits; auto.
  apply H in H9.
  simpljoin1.
  do 3 eexists; eauto .
  (*slove goal2 with H*)
  unfolds in H.
  destruct H as (H&Hx).
  destruct H as (H & H' & H6 & H6').
  intros.
  destruct H4.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H7.
  subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmsgq  (x3 :: x4) x0 pwl, x1)/\ In tid0 pwl ).
  splits; auto.
  lets Hsa : H' H7.
  simpljoin1.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8.
  inverts H8.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  apply  in_wtset_rm_notin in H9.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmsgq x y pqwaitset, qwaitset) /\ In tid0 pqwaitset ).
  splits; auto.
  lets Hsc : H' H14.
  simpljoin1.
  unfold get in H15; simpl in H15.
  rewrite H3 in H15.
  inverts H15.
  tryfalse.
  rewrite TcbMod.set_sem .
  rewrite tidspec.neq_beq_false; auto.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8.
  subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  lets Hbss :tidneq_inwt_in  pwl H7.
  destruct Hbss as (Hbss & _).
  lets Hbssc : Hbss H5.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq (x3 :: x4) y pwl, qwaitset) /\ In tid0 pwl ).
  splits; auto.
  apply H' in H4.
  simpljoin1.
  do 3 eexists; eauto.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert ( EcbMod.get v'11 eid0 = Some (absmsgq x y pqwaitset, qwaitset)/\ In tid0 pqwaitset ).
  splits; auto.
  apply H' in H9.
  simpljoin1.
  do 3 eexists; eauto .
 
 (*slove goal4 with H6'*)
  unfolds in H.
  destruct H as (H&Hx).
  destruct H as (H & H' & H6 & H6').
  intros.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H5.
  (*tid = tid0*)
  subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  (*tid <> tid0*)
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.  

  apply H6 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H12.
  subst.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :tidneq_inwt_in  x1 H5.
  destruct Hbss as (_ & Hbss).
(*   lets Hbssc : Hbss H7. *)
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 4 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 4 eexists; splits; eauto.
 
  (*slove goal4 with H6*)
  unfolds in H.
  destruct H as (H&Hx).
  destruct H as (H & H' & H6 & H6').
  intros.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H5.
  (*tid = tid0*)
  subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.
  (*tid <> tid0*)
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.  

  apply H6' in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H12.
  subst.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget.
  inverts Hget.
  lets Hbss :tidneq_inwt_in  pwl H5.
  destruct Hbss as (_ & Hbss).
  lets Hbssc : Hbss H7.
  rewrite EcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  do 4 eexists; splits; eauto.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 4 eexists; splits; eauto.

  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&H&Hx).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (abssem n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H12;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&H&Hx).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H11;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.

  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmbox n, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H11;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hhh&H&Hx).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H10;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 2 eexists;split;eauto.

  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&Hx&H& Hp).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absmutexsem n1 n2, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  rename H10 into Howp. (* new add *)
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H10;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hx&Hhh&H& Hp).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  rename H9 into Howp. (* new add *)
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H9;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  do 3 eexists;split;eauto.

  unfolds in H.
  destructs H.
  clear H H4 H5.
  elim H6; intros.
  unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
  destruct H4 as (Hx&H4).
  destruct H4 as (H4 & Howp). (* new add *)
  intros.

  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8; intros.
  subst eid.
  rewrite EcbMod.set_a_get_a in H5.
  inversion H5.
  apply CltEnvMod.beq_refl.
  rewrite EcbMod.set_a_get_a' in H5.
  2:apply tidspec.neq_beq_false; auto.

  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9.
  subst.
  rewrite TcbMod.set_a_get_a.
  lets Hin: H4 H5. destruct Hin as (_ & Hin). (* new add *)
  split; auto. (* new add *)
  do 3 eexists;eauto.
  apply CltEnvMod.beq_refl.
  rewrite TcbMod.set_a_get_a'.
  2:apply tidspec.neq_beq_false; auto.
  eapply H4;eauto.
  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct H as (_ & _ & _ & Hr4 & _).
  destruct Hr4 as (_ & _ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H.
  inverts H.
  
  splits; intros.
  destruct H4.
  unfolds in H.
  destruct H as (Hh&Hhh&Hx&Hm& H).
  destruct H.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H7;subst.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  tryfalse.
  rewrite EcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  assert (EcbMod.get v'11 eid0 = Some (absport, wls) /\ In tid0 wls).
  split;auto.
  apply H in H8.
  simpljoin1.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H9;subst.
  unfold get in H8; simpl in H8.
  rewrite H3 in H8;tryfalse.
  do 3 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eauto.

  unfolds in H.
  destruct H as (Hh&Hhh&Hx&Hm& H).
  destruct H.
  assert (tid = tid0 \/ tid <> tid0) by tauto.
  destruct H6;subst.
  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.eq_beq_true in H4; auto.
  inverts H4.

  rewrite TcbMod.set_sem in H4.
  rewrite tidspec.neq_beq_false in H4; auto.
  apply H5 in H4.
  simpljoin1.
  assert (eid = eid0 \/ eid <> eid0) by tauto.
  destruct H8;subst.
  apply ecbmod_joinsig_get in H1.
  lets Hget : EcbMod.join_get_get_r H0 H1.
  unfold get in H4; simpl in H4.
  rewrite H4 in Hget;tryfalse.
  rewrite EcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  eexists;split;eauto.
Qed.

Lemma msgqnode_p_hold_no_end_part: 
  forall b sti qens outi qend qptr qst qin qsize qblk mblk ml hml hsize wl l pwl,
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) -> 
    length ml = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil) -> 
    RLH_ECBData_P
      (DMsgQ l
             (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi)
                :: Vint32 qsize :: Vint32 qens :: Vptr qblk :: nil)
             mblk ml)
      (absmsgq (nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) ml
                         :: hml) hsize pwl, wl) ->
    (MatchLHMsgList (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil) ml hml) /\
     (MatchLHMsgLength (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil)  hml) /\
     (MatchLHMsgSize (qptr
                :: qst
                :: qend
                :: qin
                :: Vptr (b, outi  +ᵢ  Int.mul ($ 1) ($ 4))
                :: Vint32 qsize
                :: Vint32 (qens -ᵢ $ 1) :: Vptr qblk :: nil) (Int.unsigned hsize)).
Proof.
  introv Hid  Hlen Hwl Hrl .
  funfold Hwl.
  destruct Hrl.
  destruct H0 as (Hm1 & Hm2 & Hm3 & Hecb & Hm5 & Hm6).
  funfold H.
  funfold Hm1.
  funfold Hm2.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in H5.
  subst i0.
  inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  assert (Int.mul ($ 1) ($ 4) = $ 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  rewrite <- H4 in *.
  rewrite Int.repr_unsigned in *.
  assert (Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H8 in *.
  clear H5 H8.
  splits.
  unfolds.
  do 7 eexists;splits; try solve [  unfolds; simpl; eauto].
  splits.
  splits.
  introv Hlt.

  lets Hed :  math_xyz_prop2'  H1 H  Hlt; eauto.
  destruct Hed as   (Has & Hass & Hsd) .
  lets Hls : H11 Has. (* H12 -> H11 *)
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite  <- Hsd in Hls.
  rewrite <- Hass .
  eapply  vallistseg_n_m_split; eauto.
  unfold nat_of_Z.
  apply le_change.
  eapply Z2Nat.inj_le; try lia;try apply Int.unsigned_range.
  destruct H14. (* H13 -> H14 *)
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H13. (* H11 -> H13 *)
  unfold Pos.to_nat.
  simpl.
  eapply math_le_trans; eauto.
  introv Hf.
  lets Heas :math_xyz_prop3' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  destruct Hdisj as [Hd1 | Hd2].
  lets Hls : H15 Hd1. (* H14 -> H15 *)
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  lets Hrs : H16 Hd2. (* H15 -> H16 *)
  destruct Hrs.
  destruct H5 as (Hf1 & Hf2).
  inverts Hf2.
  destruct H5 as (Hf1 & Hf2).
  rewrite Hd2 in *.
  eapply vallist_seg_ltunm_prop; eauto.
  eapply list_maxsize_le; eauto.
  introv Hf.
  lets Heas :math_xyz_prop4' Hf; eauto.
  destruct Heas as (Hdisj & Hseq & He).
  assert ( Int.unsigned ($ 4) = 4).
  clear -i.
  mauto.
  rewrite H5 in *.
  clear H5.
  rewrite Hf.
  rewrite <- Hseq in *.
  rewrite <- He in *.
  lets Hres : H11 Hdisj. (* H12 -> H11 *)
  rewrite Hf in Hres.
  rewrite <- Hseq in Hres.
  rewrite vallist_seg_Sn in Hres.
  inverts Hres.
  left.
  simpl in H0.
  splits; auto.
  clear - H0.
  mauto.
  rewrite Hseq.
  rewrite <- Hf.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE in H13. (* H11 -> H13 *)
  unfold Pos.to_nat.
  simpl.
  eapply  math_le_trans; eauto.
  destruct H14; auto. (* H13 -> H14 *)
  unfolds.
  eexists.
  splits.
  unfolds; simpl;  eauto.
  eapply int_list_length_dec; auto.
  unfolds.
  eexists.
  splits; try unfolds; simpl; eauto.
  rewrite Int.repr_unsigned; auto.
Qed.

Lemma ecblist_p_post_exwt_hold1_end'':
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 (v'35:val) v'16
           v'19  v'21 v'22 v'23 v'25 v'26  x0 pwl x1 (v'0:val) v'1
          v'5 v'6 v'7 v'00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st (msg1:msg) y vhold v'86 v'82 x1' x0'
          pgrep petbl v100 (* x' *) msg2 x msg x3 sus sus',
    pgrep <> Int.zero ->
    Int.unsigned pgrep <= 255 ->
    array_type_vallist_match char_t petbl ->
    length petbl = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned pgrep)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) petbl = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P petbl (Vint32 pgrep) ->
(**)    
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 pgrep :: v100 :: nil,
                  v'13 , petbl) v'7 ->
     R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32  pgrep :: v100 :: nil,
                  v'13, petbl) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: Vptr (v'23, $ 4)
                :: v'19
                :: Vptr (v'23, v'82)
                :: Vptr (v'23, x1')
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'86 ) (absmsgq (msg1::x) x0 pwl, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq (msg1::x) x0 pwl, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    pwl <> nil ->
    (MatchLHMsgList
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (update_nth_val
            (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
            v'86 x0') (x ++ msg2 :: nil) /\
       MatchLHMsgLength
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (x ++ msg2 :: nil) /\
       MatchLHMsgSize
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, $ 4)
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (Int.unsigned x0)) ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    (V$OS_EVENT_TYPE_Q
                       :: Vint32 v'12
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0  :: Vint32 y :: v100 :: nil, v'13 ,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: Vptr (v'23, $ 4)
                              :: v'19
                              :: Vptr (v'23, $ 4)
                              :: Vptr (v'23, x3)
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) (update_nth_val
         (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v'86 x0')
) :: v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq (x++msg2::nil) x0 (remove_tid (v'58, Int.zero) pwl), x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , v'00, sus'))
.
Proof.
  intros.
  rename H23 into Hrlh. 
  rename H14 into H13'. rename H15 into H14; rename H16 into H15; rename H17 into H16; rename H18 into H17;
  rename H19 into H18; rename H20 into H19; rename H21 into H20; rename H22 into H21.
  unfolds in H20.
  destruct H20 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H4 H8.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H9.
  lets Hps : Ha1 H20 H9.
  apply tcbjoin_get_a in H19.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H19.
  destruct H19;auto.
  destruct Hps as (sts & mg & sus0 & Hget);auto.
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H19.
  inverts H19.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H13.
  destruct H13 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha'''&Ha'''').
  destruct Hb as (Hb&Hb'&Hb''&Hb'''& Hb'''').
  destruct H13' as (Hd & He).
  lets Hz : math_unmap_get_y H0 H3.
  lets Heq1 :  math_mapval_core_prop H10; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H8.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H8.
  mauto.
  rewrite H13 in H5.
  assert (PrioWaitInQ (Int.unsigned prio) petbl) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H19.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H.
  rewrite <-H13 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H0 H  H3 H5 H12.
  lia.
  auto.
  lets Hecp : Hd Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hecp in H22.
  clear Hecp.
  rename H22 into Hecp.
  destruct Hecp as (ct & nl & mg & sus0 & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H22; auto.
  lets Heqs : Ha3 H22 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmsgq (x ++ msg2 :: nil) x0 (remove_tid tid pwl), x1)  H17  H18.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  change ((v'30 ++
   (V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))) :: v'1)) with ((v'30 ++
   ((V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))):: nil) ++ v'1)).
  change ((v'31 ++
   DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: v'5)) with ((v'31 ++
   (DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: nil)++ v'5)).
   
  eapply msgqlist_p_compose2.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rename Hprs1 into Hpq.
  rename Hprs2 into Hneq.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.
  
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.

  unfolds.
  splits;
  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  simpl fst in Hc;simpl;auto.
  
  unfolds.
  splits.
  unfolds.
  unfold R_ECB_PETbl_P in Hd. 
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).

  rewrite H13 in Hprs1.
  rewrite H19 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Hd.
  lets Hxs : Hd Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.


  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in He.
  lets Hga : He Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') petbl /\ prio' <> prio) .
  splits; auto.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H24.
  rewrite H19.
  rewrite H13.
  auto.

  instantiate (1:=v'9).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H14.
  revert Heqtid.
  simpljoin1.
  intros.
  unfolds in r.
  apply r in H21.
(*   subst x. *)
  instantiate (1:=(absmsgq (x ++ msg2 :: nil) x0  (remove_tid tid pwl), x1)).
  2: eapply Hsj1.
  2:eapply Hsj2.
  splits; auto.

  unfolds.
  destruct r as (r1 & r2 &r3 & r4).
  splits. intros; auto; tryfalse. intros. auto.
  intros.
  assert( (msg1::x) = nil -> ((x ++ msg2 :: nil) = nil) ).
  {
    intros.
    destruct x;
    tryfalse.
  }
   eapply H20.
  eapply r2. auto.
  clear -r1 r2 r3 r4.
  intros.
  assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0 in H.
   apply r3 in H.
   rewrite H.
   simpl. auto.
   
   clear -r1 r2 r3 r4.
   intros.
   assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0.
   eapply r4.
   destruct pwl.
   simpl in H; tryfalse.
   auto.
Qed.

Lemma ecblist_p_post_exwt_hold1_noend'':
  forall  v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40  v'32 v'15 v'24 (v'35:val) v'16
           v'19  v'21 v'22 v'23 v'25 v'26  x0 pwl x1 (v'0:val) v'1
          v'5 v'6 v'7 v'00 v'11 v'31 v'30 v'29 v'10 v'9 prio v'62 st (msg1:msg) y vhold v'86 v'82 x1' x0'
          pgrep petbl v100 (* x' *) msg2 x msg x3 sus sus',
    pgrep <> Int.zero ->
    Int.unsigned pgrep <= 255 ->
    array_type_vallist_match char_t petbl ->
    length petbl = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned pgrep)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) petbl = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P petbl (Vint32 pgrep) ->
(**)    
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 pgrep :: v100 :: nil,
                  v'13 , petbl) v'7 ->
     R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_Q
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32  pgrep :: v100 :: nil,
                  v'13, petbl) v'7 ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'24, Int.zero))
             (v'16
                :: Vptr (v'23, $ 4)
                :: v'19
                :: Vptr (v'23, v'82)
                :: Vptr (v'23, x1')
                :: Vint32 v'21
                :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
             (v'26 :: v'25 :: nil) v'86 ) (absmsgq (msg1::x) x0 pwl, x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmsgq (msg1::x) x0 pwl, x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg, sus) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    pwl <> nil ->
    (MatchLHMsgList
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (update_nth_val
            (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
            v'86 x0') (x ++ msg2 :: nil) /\
       MatchLHMsgLength
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (x ++ msg2 :: nil) /\
       MatchLHMsgSize
         (v'16
          :: Vptr (v'23, $ 4)
             :: v'19
                :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                   :: Vptr (v'23, x3)
                      :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
         (Int.unsigned x0)) ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    (V$OS_EVENT_TYPE_Q
                       :: Vint32 v'12
                       :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0  :: Vint32 y :: v100 :: nil, v'13 ,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl
                                     (Vint32 (v'69&ᵢInt.not v'40))) :: v'1)
              (v'31 ++
                    (DMsgQ (Vptr (v'24, Int.zero))
                           (v'16
                              :: Vptr (v'23, $ 4)
                              :: v'19
                              :: Vptr (v'23, v'82 +ᵢ  Int.mul ($ 1) ($ 4))
                              :: Vptr (v'23, x3)
                              :: Vint32 v'21
                              :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
                           (v'26 :: v'25 :: nil) (update_nth_val
         (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v'86 x0')
) :: v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmsgq (x++msg2::nil) x0 (remove_tid (v'58, Int.zero) pwl), x1))
              (TcbMod.set v'7 (v'58, Int.zero)
                          (prio, rdy , v'00, sus'))
.
Proof.
  intros.
  rename H23 into Hrlh. 
  rename H14 into H13'. rename H15 into H14; rename H16 into H15; rename H17 into H16; rename H18 into H17;
  rename H19 into H18; rename H20 into H19; rename H21 into H20; rename H22 into H21.
  unfolds in H20.
  destruct H20 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H4 H8.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H9.
  lets Hps : Ha1 H20 H9.
  apply tcbjoin_get_a in H19.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H19.
  destruct H19;auto.
  destruct Hps as (sts & mg & sus0 & Hget);auto.
  unfold get in Hget; simpl in Hget.
  rewrite Hget in H19.
  inverts H19.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H13.
  destruct H13 as (Ha & Hb & Hc).
  destruct Ha as (Ha&Ha'&Ha''&Ha'''&Ha'''').
  destruct Hb as (Hb&Hb'&Hb''&Hb'''&Hb'''').
  destruct H13' as (Hd & He).
  lets Hz : math_unmap_get_y H0 H3.
  lets Heq1 :  math_mapval_core_prop H10; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H8.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H8.
  mauto.
  rewrite H13 in H5.
  assert (PrioWaitInQ (Int.unsigned prio) petbl) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H19.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H.
  rewrite <-H13 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H0 H  H3 H5 H12.
  lia.
  auto.
  lets Hecp : Hd Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_Q) = Some (V$OS_EVENT_TYPE_Q)) by auto.
  apply Hecp in H22.
  clear Hecp.
  rename H22 into Hecp.
  destruct Hecp as (ct & nl & mg & sus0 & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H22; auto.
  lets Heqs : Ha3 H22 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
  unfold get in Hcg; simpl in Hcg.
  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmsgq (x ++ msg2 :: nil) x0 (remove_tid tid pwl), x1)  H17  H18.
  destruct Hsds as ( vv & Hsj1 & Hsj2).
  change ((v'30 ++
   (V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))) :: v'1)) with ((v'30 ++
   ((V$ OS_EVENT_TYPE_Q
    :: Vint32 v'12 :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: Vint32 y :: v100 :: nil, v'13,
   update_nth_val (Z.to_nat (Int.unsigned v'38)) petbl (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢpy)))):: nil) ++ v'1)).
  change ((v'31 ++
   DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: v'5)) with ((v'31 ++
   (DMsgQ (Vptr (v'24, Int.zero))
     (v'16
      :: Vptr (v'23, $ 4)
         :: v'19
            :: Vptr (v'23, $ 4)
               :: Vptr (v'23, $ 4)
                  :: Vint32 v'21 :: Vint32 v'22 :: Vptr (v'23, Int.zero) :: nil)
     (v'26 :: v'25 :: nil)
     (update_nth_val
        (Z.to_nat ((Int.unsigned v'82 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4))
        v'86 x0') :: nil)++ v'5)).
   
  eapply msgqlist_p_compose2.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rename Hprs1 into Hpq.
  rename Hprs2 into Hneq.
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.
  
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.
  intros.
  unfolds in H24;simpl in H24;tryfalse.

  unfolds.
  splits;
  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.

  simpl fst in Hc;simpl;auto.
  
  unfolds.
  splits.
  unfolds.
  unfold R_ECB_PETbl_P in Hd. 
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).

  rewrite H13 in Hprs1.
  rewrite H19 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  unfolds in Hd.
  lets Hxs : Hd Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & sus0' & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  unfold get in Htg; simpl in Htg.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.


  intros prio' mm nn tid' sus0'.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H22.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  unfolds in He.
  lets Hga : He Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H22 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') petbl /\ prio' <> prio) .
  splits; auto.
  lets Hrs : prio_wt_inq_tid_neq  H5 H20 .
  destruct Hrs as (_ & Hrs).
  apply Hrs in H24.
  rewrite H19.
  rewrite H13.
  auto.

  instantiate (1:=v'9).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto.
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Post_Rdy_hold;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto.
  unfolds in H14.
  revert Heqtid.
  simpljoin1.
  intros.
  unfolds in r.
  apply r in H21.
(*   subst x. *)
  instantiate (1:=(absmsgq (x ++ msg2 :: nil) x0  (remove_tid tid pwl), x1)).
  2: eapply Hsj1.
  2:eapply Hsj2.
  splits; auto.

(*   destruct r as (r1 & r2 &r3 & r4).
  destruct Hrlh as (t1 & t2 & t3).
  eauto.
   destruct Hrlh as (t1 & t2 & t3).
  eauto. *)
  
  unfolds.
  destruct r as (r1 & r2 &r3 & r4).
  splits. intros; auto; tryfalse. intros. auto.
  intros.
  assert( (msg1::x) = nil -> ((x ++ msg2 :: nil) = nil) ).
  {
    intros.
    destruct x;
    tryfalse.
  }
   eapply H20.
  eapply r2. auto.
  clear -r1 r2 r3 r4.
  intros.
  assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0 in H.
   apply r3 in H.
   rewrite H.
   simpl. auto.
   
   clear -r1 r2 r3 r4.
   intros.
   assert (length (x ++ msg2 :: nil)  =  length (msg1 :: x)).
  {
      rewrite app_length.
      simpl.
      mauto.
   }
   rewrite H0.
   eapply r4.
   destruct pwl.
   simpl in H; tryfalse.
   auto.
Qed.

(*****************************************)

Lemma TCBList_P_tcb_msgvnull_hold :
    forall ptcb v1 v2 v3 v4 v5 (* v6 *) v7 v8 v9 v10 v11 rtbl vl
           tcbls prio  m sus,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::v4::v5::V$ OS_STAT_RDY::v7::v8::v9::v10::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    TCBList_P (Vptr ptcb) ((v1::v2::Vnull::Vnull::v5::V$ OS_STAT_RDY::v7::v8::v9::v10::v11::nil)::vl) rtbl
                       (TcbMod.set tcbls ptcb (prio, rdy, Vnull, sus)).
Proof.
  introv Htc Hget (* Hin *).
  unfolds in Htc.
  simpljoin1.
  simpl_hyp.
  inverts H.
  fold TCBList_P in H3.
  unfolds.
  fold TCBList_P.
  do 4 eexists; splits; eauto.
  unfolds; simpl; auto.
  instantiate (1:=(prio,rdy,Vnull, sus)).
  eapply tcbjoin_set; eauto.
  funfold H2.
  destruct x2.
  destruct p.
  destruct p.
   lets Heq : tcbjoin_get H1 Hget.
  inverts Heq.
  simpljoin1.
  simpl_hyp.
  unfolds.
  splits; try unfolds. simpl; auto.
  simpl; auto. simpl; auto.
  simpl; auto.
  unfold RL_TCBblk_P in H2.
  simpljoin1.
  exists x2 (x2&ᵢ$ 7) (x2 >>ᵢ $ 3) ($ 1<<ᵢ(x2&ᵢ$ 7)) ($ 1<<ᵢ(x2 >>ᵢ $ 3))  ($ OS_STAT_RDY).
  splits. 
  unfold V_OSTCBPrio in *; simpl in H; simpl;auto.
  unfold V_OSTCBX in *; simpl in H0; simpl;auto.
  unfold V_OSTCBY in *; simpl in H1; simpl;auto.
  unfold V_OSTCBBitX in *; simpl in H2; simpl;auto.
  unfold V_OSTCBBitY in *; simpl in H3; simpl;auto.
  unfold V_OSTCBStat in *; simpl in H4; simpl;auto.
  unfold RL_TCBblk_P in H2.
  eauto.
  splits;eauto.
  exists Vnull.
  unfold V_OSTCBEventPtr.
  simpl. splits;eauto.

  splits.
  funfold H4.
  clear - H.
  funfold H.
  unfolds.
  intros.
   assert (RdyTCBblk
        (x0
         :: v2
            :: v3
               :: m
                  :: v5 :: V$ OS_STAT_RDY :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
        rtbl prio0).
  unfolds.
  funfold H0; simpl; auto.
  apply H in H1.
  destruct H1 as (Hdly & H2).
  split;auto.
  destruct H2 as [ Hfirst | Hend ].
  left;split;auto.
  destruct Hfirst as (Hst & Heq).
  destruct Heq.
  inverts H1.
  eexists; eauto.
  
  destruct Hend as [ Hfirst | Hend ].
  right;left.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.
  destruct Hend as [ Hfirst | Hend ].
  right;right;left.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.
  destruct Hend as [ Hfirst | Hend ].
  right;right;right;left.
  destruct Hfirst as (Hst & Heq).
  inverts Hst.

  right;right;right;right.
  destruct Hend as (Hst & Heq).
  inverts Hst.
  
  {
  destruct H4 as (_ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  intros.
  inverts H.
  assert ( (prio0, rdy, m, false) = (prio0, rdy, m, false)) by auto. 
  apply Hhl in H.
  simpljoin1; try unfolds;simpl; auto.
  }

  (* new add about suspend *)
  destruct H4 as (_ & _ & Hsus & _).
  unfolds in Hsus.
  destruct Hsus as (Hrdy & Hwt).
  unfolds.
  split; intros.
  simpl_hyp.
  assert (WaitTCBblk
         (x0
          :: v2
             :: v3
                :: m
                   :: v5
                      :: V$OS_STAT_RDY
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 Int.zero).
  funfold H.
  simpl_hyp.
  (* RHL_Suspend_P *)
  destruct H4 as (_ & _ & _ & Hsus & _).
  unfolds in Hsus.
  destruct Hsus as (Hrdy & Hwt).
  unfolds.
  split; introv Heq; inverts Heq.
  eapply Hrdy; eauto.
  (* end of new add *)

  destruct H4 as (_ & _ & _ & _ & Hhl & _).
  unfolds in Hhl.
  unfolds.
  simpljoin1; splits; try unfolds;simpl; auto;
  try solve [intros; simpl_hyp].
  
  intros.
  simpl_hyp.
  unfolds in H.
  assert (Hwt: WaitTCBblk
         (x0
          :: v2
             :: Vnull
                :: Vnull
                   :: v5
                      :: V$OS_STAT_RDY
                         :: Vint32 prio :: v8 :: v9 :: v10 :: v11 :: nil)
         rtbl prio0 t).
(*   funfold H7. *)
  unfolds; simpl; auto.
  apply H in Hwt.
  destruct Hwt.
  splits; eauto.
  simpljoin1; eexists; eauto.
  unfolds; simpl; auto.

  splits; try solve [unfolds; intros; simpl_hyp].
  splits; try solve [unfolds; intros; simpl_hyp].
  unfolds.
  splits;
  try (unfolds;
  intros;
  inverts H);
  try (eapply H4; eauto).
  splits;
  try (unfolds;
  intros;
  inverts H).
Qed.

Lemma RH_TCBList_ECBList_P_high_get_vnull_hold :
  forall ecbls tcbls pcur  m  prio  m' sus sus',
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    TcbMod.get tcbls pcur = Some (prio, rdy, m', sus) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcbls pcur (prio, rdy, m, sus')) pcur. 
Proof.
  introv Hr (* Ht *) He.
  unfolds in Hr.
  destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4& Hr5).
  unfolds.
  splits.
  splits.  
  intros.

  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr1 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply Hr1 in H.
  simpljoin1.
  do 3 eexists; eauto.

  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr1 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply Hr1 in H.
  simpljoin1.
  do 3 eexists; eauto.
  
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  eauto.

  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr1 in H.
  eauto.
  
  splits.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr2 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply Hr2 in H.
  simpljoin1.
  do 3 eexists; eauto.
  
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr2 in H.
  eauto.

  splits.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr3 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply Hr3 in H.
  simpljoin1.
  do 3 eexists; eauto.
  
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr3 in H.
  eauto.
  
  splits.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr4 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  apply Hr4 in H.
  simpljoin1.
  do 3 eexists; eauto.
  
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr4 in H.
  eauto.

  apply Mutex_owner_hold_for_set_tcb.
  unfold RH_TCBList_ECBList_MUTEX_P in Hr4.
  simpljoin1.
  eauto.
   (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  destruct Hr4 as (_ & _ & _ & Hrb).
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  
  splits.
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  subst.
  apply Hr5 in H.
  simpljoin1.
  unfold get in H; unfold TcbMap in H.
  rewrite H in He. inverts He.
  rewrite TcbMod.set_sem ;
   rewrite tidspec.neq_beq_false; auto.
  apply Hr5 in H.
  simpljoin1.
  do 3 eexists; eauto.
  
  intros.
  assert (tid = pcur \/ tid <> pcur) by tauto.
  destruct H0.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; auto.
  inverts H.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; auto.
  apply Hr5 in H.
  eauto.
Qed.

Lemma get_tcb_stat_q
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_q sid) (Some wt) ->
  wt <> Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_Q)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
  intros.
  funfold H.
  fold TCBList_P in H6.
  inverts H.
  destruct x2. destruct p.
  destruct p.
  lets Hget: tcbjoin_get_a H4.
  rewrite H0 in Hget.
  inverts Hget.
  funfold H5.
  funfold H5.
  rename H5 into Hsus1; rename H10 into Hsus2;
  rename H11 into H5; rename H12 into H10.
  funfold H10.
  funfold  H12.
  specialize ( H12 _ _ _ _ (eq_refl _) ).
  simpljoin.
  unfold WaitTCBblk in *.
  destruct H12 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
  inverts Heq.
  destruct Hcase as [Hnz | (Hz & _)]; try subst; tryfalse.
  simpljoin.
  splits; auto.
Qed.

Lemma get_tcb_stat_q_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_q sid) (Some wt) ->
  wt <> Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_Q))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_q; eauto.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H12.
specialize (H19 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H19 as [ (t & Heq & Hwt) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_q_eq0
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_q sid) (Some wt) ->
  wt = Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_Q)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_in_tbl prio rtbl.
Proof.
  intros.
  funfold H.
  fold TCBList_P in H6.
  inverts H.
  destruct x2. destruct p.
  destruct p.
  lets Hget: tcbjoin_get_a H4.
  rewrite H0 in Hget.
  inverts Hget.
  funfold H5.
  funfold H5.
  rename H5 into Hsus1; rename H9 into Hsus2;
  rename H10 into H5; rename H11 into H9.
  funfold H9.
  funfold  H11.
  specialize ( H11 _ _ _ _ (eq_refl _) ).
  simpljoin.
  unfold RdyTCBblk in *.
  destruct H11 as [ (Heq & Hcase) | (Hf & Hwait)]; tryfalse.
  inverts Heq.
  destruct Hcase as [(Hnz & _) | (_ & Hz)]; tryfalse.
  simpljoin.
  splits; auto.
Qed.

Lemma get_tcb_stat_q_eq0_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid wt,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, true) ->
  st = wait (os_stat_q sid) (Some wt) ->
  wt = Int.zero ->
  V_OSTCBStat tcurl = Some (Vint32 (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 wt) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H6.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H4.
rewrite H0 in Hget.
inverts Hget.
funfold H5.
funfold H5.
funfold H11.
specialize (H18 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H18 as [ (t & Heq & Hwt) | (Heq & _)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma get_tcb_stat_q_none
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, false) ->
  st = wait (os_stat_q sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_Q)) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
rename H4 into Hsus1; rename H9 into Hsus2;
rename H10 into H4; rename H11 into H9.
funfold H9.
funfold H11.
specialize (H11 _ _ _ _ (eq_refl _)).
simpljoin.
unfold WaitTCBblk in *.
destruct H11 as [ (Hf & _) | (_ & Hwait)]; tryfalse.
simpljoin.
splits; auto.
Qed.

Lemma get_tcb_stat_q_none_sus
: forall tcur tcurl tcblist rtbl tcbls prio st msg sid sus,
  TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
  TcbMod.get tcbls tcur = Some (prio, st, msg, sus) ->
  st = wait (os_stat_q sid) None ->
  V_OSTCBStat tcurl = Some (Vint32 (if sus then (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)) else ($ OS_STAT_Q))) /\
  V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
  V_OSTCBDly tcurl = Some (Vint32 Int.zero) /\
  prio_not_in_tbl prio rtbl.
Proof.
intros.
destruct sus.
2: eapply get_tcb_stat_q_none; eauto.
funfold H.
fold TCBList_P in H5.
inverts H.
destruct x2. destruct p.
destruct p.
lets Hget: tcbjoin_get_a H3.
rewrite H0 in Hget.
inverts Hget.
funfold H4.
funfold H4.
funfold H11.
specialize (H18 _ _ _ _ (eq_refl _)).
simpljoin.
destruct H18 as [ (t & Heq & Hwt) | (Heq & Hwt)]; inverts Heq.
funfold Hwt.
splits; auto.
Qed.

Lemma RLH_ECB_ETbl_P_hold_for_update_q_to_st
: forall tcbls ct p qid msg osevent etbl ey egrp' st petbl sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 &Hra5).

unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5];
unfold V_OSEventType in *;
intros;
assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto);
destruct Hpr1 as (Hpr1 & Hpr2);
lets Hvp: int_usign_eq Hpr1 Hpr2;
rewrite <- Hvp in H;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= $ prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi in H;
clear H1 Hpi;
rewrite Hvp in H;
destruct H;
assert (nq1: 0%nat <> 1%nat) by pauto;
lets Heq1: nth_upd_neq nq1 H0;
[ lets Hst: Hra1 H Heq1| lets Hst: Hra2 H Heq1 | lets Hst: Hra3 H Heq1 | lets Hst: Hra4 H Heq1 | lets Hst: Hra5 H Heq1];
destruct Hst as [tid]; do 3 destruct H2;
unfold get in *; unfold TcbMap in *;
exists tid x x0;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
rewrite Htg in H2;
inverts H2);
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma RLH_ECB_ETbl_P_hold_for_update_q_to_st'
: forall tcbls ct p qid wt msg osevent etbl petbl ey egrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
unfolds;
splits;
unfolds;
[ funfold Hra1 | funfold Hra2 | funfold Hra3 | funfold Hra4 | funfold Hra5];
unfold V_OSEventType in *;
intros;
assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto);
destruct Hpr1 as (Hpr1 & Hpr2);
lets Hvp: int_usign_eq Hpr1 Hpr2;
rewrite <- Hvp in H;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= $ prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi in H;
clear H1 Hpi;
rewrite Hvp in H;
destruct H;
assert (nq1: 0%nat <> 1%nat) by pauto;
lets Heq1: nth_upd_neq nq1 H0;
[ lets Hst: Hra1 H Heq1| lets Hst: Hra2 H Heq1 | lets Hst: Hra3 H Heq1 | lets Hst: Hra4 H Heq1 | lets Hst: Hra5 H Heq1];
destruct Hst as [tid]; do 3 destruct H2;
unfold get in *; unfold TcbMap in *;
exists tid x x0;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
rewrite Htg in H2;
inverts H2);
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_q_to_rdy
: forall tcbls ct p qid msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
unfolds;
splits;
unfolds;
[ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4 | funfold Hrb5];
unfold V_OSEventType in *;
destruct Hrpt as (_ & _ & Hrpt);
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
[ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H | try eapply Hrb5 in H];
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma RLH_ECB_PETbl_P_hold_for_update_q_to_st
: forall tcbls ct p qid msg osevent etbl ey egrp' st petbl sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_PETbl_Q_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
rename Hre into Hra1.
unfolds.
funfold Hra1.
unfold V_OSEventType in *.
intros.
eapply Hra1 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.
Qed.

Lemma RHL_ECB_PETbl_P_hold_for_update_q_to_rdy
: forall tcbls ct p qid msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_PETbl_Q_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
rename Hre into Hrb1.
unfolds.
funfold Hrb1.
unfold V_OSEventType in *.
destruct Hrpt as (_ & _ & Hrpt).
funfold Hrpt.
intros.
unfold get in *; unfold TcbMap in *.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H0.
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H).
eapply neq_set_get  with (MC := TcbMap)in H0 .
unfold get in H0. simpl in H0.
rewrite H0 in H.
eapply Hrb1 in H.
destruct H.
splits.
auto.
destruct osevent;
simpl;simpl in H1;auto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_q_to_rdy
: forall tcbls ct p qid msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_q_to_st; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_q_to_rdy; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma R_ECB_PETbl_P_hold_for_update_q_to_rdy
: forall tcbls ct p qid msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, rdy , msg, sus) ->
      R_ECB_PETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_PETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_PETbl_P_hold_for_update_q_to_st; try eauto.
eapply RHL_ECB_PETbl_P_hold_for_update_q_to_rdy; try eauto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_q_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  simpljoin1.
  splits; auto.
  
  intros.
  simpl in H.
  simpljoin1.
  destruct msgql; tryfalse.
  destruct a.
  simpljoin1.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra1 & Hra2 & Hra3 & Hra4 & Hra5).
  destruct Hr2 as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits.
  
  unfolds.
  destruct p.
  intros.
  eapply Hra1 in H2;eauto.
  simpljoin1.
  assert (x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H8.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H0 in H2.
  inverts H2.
  exists x0 x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  unfolds.
  destruct p.
  intros.
  eapply Hra2 in H2;eauto.
  simpljoin1.
  assert (x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H8.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H0 in H2.
  inverts H2.
  exists x0 x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  unfolds.
  destruct p.
  intros.
  eapply Hra3 in H2;eauto.
  simpljoin1.
  assert (x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H8.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H0 in H2.
  inverts H2.
  exists x0 x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  unfolds.
  destruct p.
  intros.
  eapply Hra4 in H2;eauto.
  simpljoin1.
  assert (x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H8.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H0 in H2.
  inverts H2.
  exists x0 x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  unfolds.
  destruct p.
  intros.
  eapply Hra5 in H2;eauto.
  simpljoin1.
  assert (x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H8.
  subst.
  unfolds in H2; simpl in H2.
  rewrite H0 in H2.
  inverts H2.
  exists x0 x1 x2.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  destruct p.
  simpljoin1.
  unfolds.
  splits.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H7.
  subst.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; eauto.
  inverts H6.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; eauto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H7.
  subst.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; eauto.
  inverts H6.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; eauto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H7.
  subst.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; eauto.
  inverts H6.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; eauto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H7.
  subst.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; eauto.
  inverts H6.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; eauto.
  
  unfolds.
  intros.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H7.
  subst.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.eq_beq_true in H6; eauto.
  inverts H6.
  rewrite TcbMod.set_sem in H6.
  rewrite tidspec.neq_beq_false in H6; eauto.
  
  simpl. destruct p.
  simpl.
  auto.
  unfolds.
  unfold R_ECB_PETbl_P in H3.
  destruct H3 as (Hra & Hrb).
  unfold RLH_ECB_PETbl_Q_P in Hra.
  splits.
  unfolds.
  destruct p.
  intros.

  eapply Hra in H;eauto.
  destruct H.
  destruct H.
  destruct H.
  destruct H. rename x3 into sus0.
  exists x0 x1 x2.
  assert(x0 = ptcb \/ x0 <> ptcb) by tauto.
  destruct H5. 
  subst.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfold get in H.
  unfold TcbMap in H.
  rewrite H in H0.
  tryfalse.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  unfold RHL_ECB_PETbl_Q_P.
  destruct p.
  intros.

  unfold RHL_ECB_PETbl_Q_P in Hrb.
  assert(tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H3.
  subst.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.eq_beq_true in H; eauto.
  tryfalse.
  rewrite TcbMod.set_sem in H.
  rewrite tidspec.neq_beq_false in H; eauto.
  destruct p.
  simpljoin1.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_q_to_rdy
: forall tcbls ct p qid wt msg ecbls m n wls pwls sus sus',
  TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq m n pwls, wls) ->
  In ct wls ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  RH_TCBList_ECBList_P (EcbMod.set ecbls qid (absmsgq m n pwls, remove_tid ct wls)) 
                                                    (TcbMod.set tcbls ct (p, rdy, msg, sus')) ct.
Proof.
introv Htg Heg Hi Hrte.
destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
unfolds;
splits;
unfolds;
[ funfold Hr1;
  rename H0 into Hpostq1; rename H1 into H0; rename H2 into Hpostq2
 | funfold Hr2 | funfold Hr3 | funfold Hr4; rename H2 into Hownp | funfold Hr5];
(* [ funfold Hr1 | funfold Hr2 | funfold Hr3 | funfold Hr4]; *)
try splits;
intros; try( rename H0 into H'; rename H1 into H0;
rename H2 into H0' ; rename H3 into H1);

try (assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H1;
destruct H2;
try (subst;
rewrite EcbMod.beq_refl in H1;
destruct H1;
inverts H1);
try (rewrite tidspec.neq_beq_false in H1; try auto;
try eapply H in H1;
try eapply Hpostq1 in H1;
do 4 destruct H1;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H1;
inverts H1);
rewrite tidspec.neq_beq_false; try eauto)).

Focus 7.
{
  assert (eid = qid \/ eid <> qid) by tauto;
 rewrite EcbMod.set_sem in H2;
destruct H3;
try (subst;
rewrite EcbMod.beq_refl in H2;
destruct H2;
inverts H2);
try (rewrite tidspec.neq_beq_false in H2; try auto;
eapply H in H2;
do 4 destruct H2;
rewrite TcbMod.set_sem;
assert (Ht: tid = ct \/ tid <> ct) by tauto;
destruct Ht;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Htg in H2;
inverts H2);
rewrite tidspec.neq_beq_false; try eauto).
}
Unfocus.
3:{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply H0 in H1.
do 4 destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1.
destruct H1; inverts H1.
rewrite EcbMod.beq_refl.
exists x x0 x1 (remove_tid ct x2).
split; auto.
eapply tidneq_inwt_in with (x1:= x2) in H2.
rewrite <- H2 in H3. auto.
rewrite tidspec.neq_beq_false; try eauto.
}

4:{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do 2 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
4:{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto;
try (eapply H0 in H1;
do 2 destruct H1;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H3;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H1;
destruct H1;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}
4:{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H3;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H2; try auto;
try (eapply H0 in H2;
do 3 destruct H2;
 assert (eid = qid \/ eid <> qid) by tauto;
destruct H4;
try (subst;
unfold get in *; unfold TcbMap,EcbMap in *;
rewrite Heg in H2;
destruct H2;
tryfalse);
rewrite tidspec.neq_beq_false; try eauto).
}

3:{
rewrite TcbMod.set_sem in *;
rewrite EcbMod.set_sem;
assert (ct = tid \/ ct <> tid) by tauto;
destruct H2;
try(subst;
rewrite TcbMod.beq_refl in *;
tryfalse);
rewrite tidspec.neq_beq_false in H1; try auto.
eapply Hpostq2 in H1.
do 4 destruct H1.
 assert (eid = qid \/ eid <> qid) by tauto.
destruct H3.
subst.
unfold get in *; unfold TcbMap,EcbMap in *.
rewrite Heg in H1.
destruct H1.
inverts H1.
rewrite TcbMod.beq_refl.
exists x x0 x1 (remove_tid ct x2).
splits;eauto.
rewrite tidspec.neq_beq_false; try eauto.
}
 Focus 2.
  intros.
  assert (tid = ct \/ tid <> ct) by tauto.
  destruct H1.
  subst.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pqwaitset, wls) /\ In ct pqwaitset).
  splits;eauto.
  apply Hpostq1 in H1.
  simpljoin1.
  unfold get in H1; unfold TcbMap in H1.
  rewrite H1 in Htg. inverts Htg.
  rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; auto.
  assert (EcbMod.get ecbls qid = Some (absmsgq x y pqwaitset, wls) /\ In tid pqwaitset).
    splits;eauto.
  apply Hpostq1 in H3.
  simpljoin1.
  do 3 eexists; eauto.
  
  rewrite TcbMod.set_sem.
  assert (ct = tid \/ ct <> tid) by tauto.
  destruct H1.
  subst. eapply in_remove_tid_false in H2. tryfalse.
  rewrite tidspec.neq_beq_false; try auto.
  eapply H.
  split; try eauto.
  eapply tidneq_inwt_in with (x1:= wls) in H1.
  rewrite H1 in H2. auto.

  eapply rh_tcblist_ecblist_mutex_owner_set'; eauto.
  apply Mutex_owner_hold_for_set_tcb; auto.
  (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *)
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb;
  try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  pure_auto.
  do 2 destruct H2.
  inverts H2.

  rewrite TcbMod.set_sem in *;
  rewrite EcbMod.set_sem;
  assert (ct = tid \/ ct <> tid) by tauto;
  destruct H2;
  try(subst;
  rewrite TcbMod.beq_refl in *;
  tryfalse);
  rewrite tidspec.neq_beq_false in H1; try auto;
  try (eapply H0 in H1;
  destruct H1;
  assert (eid = qid \/ eid <> qid) by tauto;
  destruct H3;
  try (subst;
  unfold get in *; unfold TcbMap,EcbMap in *;
  rewrite Heg in H1;
  destruct H1;
  tryfalse);
  rewrite tidspec.neq_beq_false; try eauto).
Qed.

Lemma RHL_ECB_ETbl_P_hold_for_update_q_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_ETbl_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4 & Hrb5).
unfolds;
splits;
unfolds;
[ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4 | funfold Hrb5];
unfold V_OSEventType in *;
destruct Hrpt as (_ & _ & Hrpt);
funfold Hrpt;
intros;
unfold get in *; unfold TcbMap in *;
assert (tid = ct \/ tid <> ct) by tauto;
destruct H0;
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H);
rewrite tidspec.neq_beq_false in H; try auto;
pose proof prio_wt_inq_tid_neq;
specialize H1 with (prio':= prio);
lets Hpi: H1 Hey Hpr;
rewrite Hpi;
clear Hpi;
lets Hnp: Hrpt H0 H Htg;
[ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H | try eapply Hrb5 in H];
splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_q_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
      R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_ETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_ETbl_P_hold_for_update_q_to_st'; try eauto.
eapply RHL_ECB_ETbl_P_hold_for_update_q_to_rdy'; try eauto.
simpl in *.
eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma RLH_ECB_PETbl_P_hold_for_update_q_to_st'
: forall tcbls ct p qid wt msg osevent etbl petbl ey egrp' st sus sus',
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RLH_ECB_PETbl_Q_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, st, msg, sus')).
Proof.
introv Hpr Htg Hey Hre.
rename Hre into Hra1.
(* destruct Hre as (Hra1 & Hra2 & Hra3 & Hra4).folds; *)
unfolds.
funfold Hra1.
unfold V_OSEventType in *.
intros.
eapply Hra1 in H.
simpljoin1.
exists x x0 x1.
assert (x = ct \/ x <> ct) by tauto.
destruct H1.
subst.
unfold get in H;simpl in H.
rewrite Htg in H.
inverts H.
rewrite TcbMod.set_sem;
rewrite tidspec.neq_beq_false; eauto.
unfold update_nth_val in H0.
simpl in H0.
destruct osevent.
auto.
simpl in H0.
simpl;auto.
Qed.

Lemma RHL_ECB_PETbl_P_hold_for_update_q_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl sus sus',
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_PETbl_Q_P qid (osevent,etbl,petbl) tcbls ->
    RHL_ECB_PETbl_Q_P qid
     (update_nth_val 1 osevent (Vint32 egrp'),
      update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
      (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl)
      (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hrpt Htg Hey Hre.
rename Hre into Hrb1.
unfolds.
funfold Hrb1.
unfold V_OSEventType in *.
destruct Hrpt as (_ & _ & Hrpt).
funfold Hrpt.
intros.
unfold get in *; unfold TcbMap in *.
assert (tid = ct \/ tid <> ct) by tauto.
destruct H0.
rewrite TcbMod.set_sem in H;
try (subst;
rewrite TcbMod.beq_refl in H;
inverts H).
eapply neq_set_get  with (MC := TcbMap)in H0 .
unfold get in H0. simpl in H0.
rewrite H0 in H.
eapply Hrb1 in H.
destruct H.
splits.
auto.
destruct osevent;
simpl;simpl in H1;auto.
Qed.

Lemma R_ECB_PETbl_P_hold_for_update_q_to_rdy'
: forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl sus sus',
      Int.unsigned p < 64 ->
      y = p >>ᵢ $ 3 ->
      bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
      R_PrioTbl_P ptbl tcbls vhold ->
      TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
      R_ECB_PETbl_P qid (osevent, etbl,petbl) tcbls ->
      nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
      R_ECB_PETbl_P qid
       (update_nth_val 1 osevent (Vint32 egrp'),
         update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl)
       (TcbMod.set tcbls ct (p, rdy, msg, sus')).
Proof.
introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
funfold Hre.
unfolds.
splits.
eapply RLH_ECB_PETbl_P_hold_for_update_q_to_st'; try eauto.
eapply RHL_ECB_PETbl_P_hold_for_update_q_to_rdy'; try eauto.
Qed.

Lemma RLH_ECBData_P_hold_q
: forall n ct w ecbcurl m pw,
  RLH_ECBData_P ecbcurl (absmsgq m n pw, w) ->
RLH_ECBData_P ecbcurl (absmsgq m n pw, remove_tid ct w).
Proof.
intros.
unfolds.
unfolds in H.
destruct ecbcurl; try tryfalse.
splits; pauto.
simpl in *.
simpljoin.
splits; intros.
apply H2 in H6.
destruct w.
simpl;auto.
inverts H6.
eapply H3.
destruct w.
simpl in H6;tryfalse.
auto.
eapply H4;auto.
eapply H5;auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_q_to_rdy':
  forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time sus sus',
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_q qid) time, m, sus) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
              (TcbMod.set tcbls ptcb (prio, rdy, m, sus')).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  simpljoin.
  destruct msgql; tryfalse.
  destruct a.
  destruct p.
  simpljoin.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4 & Hra5).
  destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4 & Hrb5).
  simpl in Hr3.
  splits.
  unfolds.
  splits;
  unfolds;
  intros;
  rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  rename H7 into H6;
  [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6 | eapply Hra5 in H6];
  simpljoin; eauto;
   assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
  destruct H7;
  try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6;
    eapply EcbMod.join_sig_get in H3;
    rewrite H3 in H1;
    inverts H1);
    try (subst;
    unfold get in H6; simpl in H6;
    rewrite H0 in H6;
    inverts H6);
    repeat eexists;
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
   rename H3 into H3';
  rename H4 into H3;
  rename H5 into H4;
  rename H6 into H5;
  unfolds;
  splits;
  unfolds;
  intros;
  assert (tid = ptcb \/ tid <> ptcb) by tauto;
    destruct H6;
    try subst;
    rewrite TcbMod.set_sem in H2;
    try (rewrite TcbMod.beq_refl in H2; inverts H2);
    rewrite tidspec.neq_beq_false in H2; eauto.
    simpl; auto.
    
  unfolds;
  splits;
  unfolds;
  intros.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RLH_ECB_PETbl_Q_P in H3.
  eapply H3 in H7.
  2:eauto.
  simpljoin1.
  exists x3 x4 x5.
  assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
  destruct H10.
  subst.
  unfold get in H7;simpl in H7.
  rewrite H7 in H0.
  inverts H0.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false.  eauto.
  eauto.
  unfold R_ECB_PETbl_P in H3.
  simpljoin1.
  unfold RHL_ECB_PETbl_Q_P in H8.
  assert (tid = ptcb \/ tid <> ptcb) by tauto.
  destruct H9.
  subst.
  rewrite TcbMod.set_sem in H7.
  rewrite TcbMod.beq_refl in H7; inverts H7.
  rewrite TcbMod.set_sem in H7.
  rewrite tidspec.neq_beq_false in H7; eauto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ECBList_P_hold_for_update_q_to_rdy'
: forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
              tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold n m pwls wls petbl sus sus',
    Int.unsigned p < 64 ->
   y = p >>ᵢ $ 3 ->
   bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
  R_PrioTbl_P ptbl tcbls vhold ->
  length els1 = length ecblist1 ->
  RH_TCBList_ECBList_P ecbls tcbls ct ->
  TcbMod.get tcbls ct = Some (p, wait (os_stat_q qid) wt, msg, sus) ->
  EcbMod.get ecbls qid = Some (absmsgq m n pwls, wls) ->
  In ct wls ->
  get_ectr (Vptr qid) head els1  = None ->
  get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
  ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
  nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
  osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
  etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
  ECBList_P head Vnull (els1 ++ ((osevent',etbl',petbl) :: nil) ++ els2) 
                        (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
                         (EcbMod.set ecbls qid (absmsgq m n pwls, remove_tid ct wls))
                        (TcbMod.set tcbls ct (p, rdy, msg, sus'))
.
Proof.
introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
introv Hgptr2 Hep Hey Het' Hetbl'.
assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
destruct Hels1.
subst els1.
assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ecblist1.
simpl in *.
q_common.mytac.
destruct (beq_addrval qid x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
apply beq_addrval_eq in eq1.
subst x.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_q_to_rdy'; try eauto.
eapply R_ECB_PETbl_P_hold_for_update_q_to_rdy'; try eauto.
exists (absmsgq m n pwls, remove_tid ct wls) x1 x2.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H3.
destruct x0.
rewrite Heg in Heg'.
inverts Heg'.
eapply RLH_ECBData_P_hold_q; auto.
eapply ECBList_P_high_tcb_block_hold_q_to_rdy'; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
(* els1 <> nil *)
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
simpljoin.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
eapply ecblist_p_compose; try eauto.
Focus 2.
eapply ECBList_P_high_tcb_block_hold_q_to_rdy'; try eauto.
eapply ejoin_get_none_l; [idtac | eauto].
eapply EcbMod.join_sig_get; eauto.
eapply EcbMod.my_joinsig_join_set; try eauto.
simpl.
exists qid.
splits; try auto.
eapply R_ECB_ETbl_P_hold_for_update_q_to_rdy'; try eauto.
eapply R_ECB_PETbl_P_hold_for_update_q_to_rdy'; try eauto.
exists (absmsgq m n pwls, remove_tid ct wls) x4 x5.
splits; try auto.
unfold V_OSEventListPtr in *.
eapply nth_upd_neqrev; try pauto.
unfold sig. unfold EcbMap.
eapply EcbMod_get_join_sig_set; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
lets Heg': EcbMod.join_sig_get H7.
destruct x3.
lets Heg2: EcbMod.join_get_r H2 Heg'.
rewrite Heg in Heg2.
inverts Heg2.
eapply RLH_ECBData_P_hold_q; auto.
eapply ECBList_P_high_tcb_block_hold_q_to_rdy'; try eauto.
eapply ejoin_get_none_r; [idtac | eauto].
eapply EcbMod.map_get_sig.
Qed.


