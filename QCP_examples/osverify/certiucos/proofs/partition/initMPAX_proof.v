Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import abs_op.
Require Import inv_prop.
Require Import os_inv.
Require Import ifun_spec.
Require Import CapPure.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_code_defs.
Require Import seplog_trm_tacs.
Require Import gjb_common.
Require Import Aarray_new_common.
Require Import cast_int_ptr_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Require Import partition_common.
Require Import MPAX_common.
Require Import MPAX_pure.
Require Import csl_mpax_pure.
Require Import MPAX_pure.
Require Import partition_CPU.
Require Import abs_op_partition_ext.
Require Import abs_infer_abt.


Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Local Open Scope list_scope.

Ltac sep_get_rv_array_struct_gen :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        introv Hsat;
        eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  | Hsat:?s |= ?P
    |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
       eapply struct_array_member_rv';
                [ try symbolic_execution
                | try symbolic_execution
                | match goal with
                  | |- ((?te = _) \/ _) =>
                        match te with
                         | Tarray ?tp _ => try unfold tp
                         | Tptr ?tp => try unfold tp
                         | _ => idtac
                         end
                  end;auto
                | auto
                | try  match goal with
                            | Hsat:_ |= ?P'
                              |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                                  match find_ptrstruct_by_block P' pb with
                                  | some ?n => sep lifts (n :: nil) in Hsat
                                  end
                            end; try simpl typelen; try sep cancel Astruct; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; eauto
                | simpl; auto
                | try apply int_ltu_zero_eq_false
                | try solve_part_int_rgn
                | simpl; try solve_part_int_rgn
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | simpl nth_val'; auto ]
  end.

Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.

(*---------------------------------------*)

Lemma initmpax_absimp_cdom_err:
forall P sch s1 s2 kscurd,
   can_change_aop P ->
   kscurd = Int.mone ->
   absinfer sch 
            (<|| (ksCurDomain_err (|nil|) ;; s2) ?? s1 ||> ** HKsCurDomain kscurd ** P)
            (<|| s2 ||> ** HKsCurDomain kscurd ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_cdom_cons:
forall P sch s1 s2 kscurd,
   can_change_aop P ->
   kscurd <> Int.mone ->
   absinfer sch 
            (<|| (ksCurDomain_err (|nil|) ;; s2) ?? s1 ||> ** HKsCurDomain kscurd ** P)
            (<|| s1 ||> ** HKsCurDomain kscurd ** P).
Proof.
intros.
subst.
eapply absinfer_choice2;try can_change_aop_solver.
eauto.
Qed.


Lemma initmpax_absimp_get_rtsk_baddr:
forall P sch s absks kscurd rv_baddr vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst b i type i' voff,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   RootTaskStk_head = (b,i) -> 
   type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
   i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) ->
   voff = Int.shru (ptr_to_int32 (b, i')) (Int.repr 12) ->
   rv_baddr = Vint32 voff ->
   absinfer sch 
            (<|| get_rtsk_baddr (|rv_baddr :: nil|) ;; s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_get_rtsk_baddr_abt:
forall P sch s absks kscurd rv_baddr vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst b i type i' voff,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   RootTaskStk_head = (b,i) -> 
   type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
   i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) ->
   voff = Int.shru (ptr_to_int32 (b, i')) (Int.repr 12) ->
   rv_baddr <> Vint32 voff ->
   absinfer sch 
            (<|| get_rtsk_baddr (|rv_baddr :: nil|) ;; s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| ABORT ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
assert (Hc: can_change_aop
            (HKsCurDomain kscurd ** HKsDomains absks ** P)) by
        can_change_aop_solver.
eapply absinfer_trans;
[ idtac |
  eapply absinfer_seq_abt;[ | | eauto]; try eauto].
eapply absinfer_seq; try eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver;
instantiate(2:= get_rtsk_baddr (|rv_baddr :: nil|));
instantiate(2:= s0);
sep pauto.
Qed.

Lemma initmpax_absimp_set_mpaxh:
forall P sch q t evheap vsize vbaddr l l' s,
   can_change_aop P ->
   Get_struct evheap q = Some (q, t, l) ->
   l' = vbaddr:: vsize :: nil ->
   absinfer sch 
          (<|| set_mpaxh(|(Vptr q) :: vbaddr:: vsize :: nil|) ;; s||> 
          ** HEvStructHeap evheap ** P)
          (<|| s ||>
          ** HEvStructHeap (Set_struct evheap q t l') ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_get_rtsk_raddr:
forall P sch s absks kscurd rv_raddr vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst b i type i' voff voff',
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   RootTaskStk_head = (b,i) -> 
   type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
   i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) ->
   voff = ptr_to_int32 (b, i') ->
   voff' = (if Int.ltu voff (Int.repr (0x80000000))
            then Int.shru voff (Int.repr 12)
            else Int.or (Int.shru (Int.sub voff (Int.repr (0x80000000)))
                                  (Int.repr 12))
                        (Int.repr (0x800000))) ->
   rv_raddr = Vint32 voff' ->
   absinfer sch 
            (<|| get_rtsk_raddr (|rv_raddr :: nil|) ;; s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_get_rtsk_raddr_abt:
forall P sch s absks kscurd rv_raddr vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst b i type i' voff voff',
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   RootTaskStk_head = (b,i) -> 
   type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) ->
   i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) ->
   voff = ptr_to_int32 (b, i') ->
   voff' = (if Int.ltu voff (Int.repr (0x80000000))
            then Int.shru voff (Int.repr 12)
            else Int.or (Int.shru (Int.sub voff (Int.repr (0x80000000)))
                                  (Int.repr 12))
                        (Int.repr (0x800000))) ->
   rv_raddr <> Vint32 voff' ->
   absinfer sch 
            (<|| get_rtsk_raddr (|rv_raddr :: nil|) ;; s ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| ABORT ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
assert (Hc: can_change_aop
            (HKsCurDomain kscurd ** HKsDomains absks ** P)) by
        can_change_aop_solver.
eapply absinfer_trans;
[ idtac |
  eapply absinfer_seq_abt;[ | | eauto]; try eauto].
eapply absinfer_seq; try eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
instantiate(2:= get_rtsk_raddr (|rv_raddr :: nil|));
instantiate(2:= s0);
sep pauto.
Qed.

Lemma initmpax_absimp_set_mpaxl:
forall P sch q t evheap vraddr vsr vsw vsx vur vuw vux l l' s,
   can_change_aop P ->
   Get_struct evheap q = Some (q, t, l) ->
   l' = vraddr :: vsr :: vsw :: vsx :: vur :: vuw :: vux :: nil ->
   absinfer sch 
          (<|| set_mpaxl(|(Vptr q) :: vraddr :: vsr :: vsw :: 
                           vsx :: vur :: vuw :: vux :: nil|) ;; s||> 
          ** HEvStructHeap evheap ** P)
          (<|| s ||>
          ** HEvStructHeap (Set_struct evheap q t l') ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.


Lemma initmpax_absimp_get_ksdom_size_vaddr:
forall P sch s absks kscurd vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst voff rv_size rv_vaddr,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   voff = Int.shru vaddr (Int.repr 12) ->
   rv_size = Vint32 vsize ->
   rv_vaddr = Vint32 voff ->
   absinfer sch 
            (<|| get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;; 
                 s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_get_ksdom_size_vaddr_abt:
forall P sch s absks kscurd vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst voff rv_size rv_vaddr,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   voff = Int.shru vaddr (Int.repr 12) ->
   ~(rv_size = Vint32 vsize /\ rv_vaddr = Vint32 voff) ->
   absinfer sch 
            (<|| get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;; 
                 s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| ABORT ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
assert (Hc: can_change_aop
            (HKsCurDomain kscurd ** HKsDomains absks ** P)) by
        can_change_aop_solver.
eapply absinfer_trans;
[ idtac |
  eapply absinfer_seq_abt;[ | | eauto]; try eauto].
eapply absinfer_seq; try eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
instantiate(2:= get_rtsk_raddr (|rv_vaddr :: rv_size :: nil|));
instantiate(2:= s0);
sep pauto.
Qed.

Lemma initmpax_absimp_get_ksdom_paddr:
forall P sch s absks kscurd vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst voff rv_paddr,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   voff = Int.shru vpaddr (Int.repr 12) ->
   rv_paddr = Vint32 voff ->
   absinfer sch
            (<|| get_ksdom_paddr (| rv_paddr :: nil |) ;; 
                 s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
infer_solver 0%nat.
Qed.

Lemma initmpax_absimp_get_ksdom_paddr_abt:
forall P sch s absks kscurd vdom vid vperiod vpaddr vaddr
       vlen vsize vstatus vintst voff rv_paddr,
   can_change_aop P ->
   KsDomsMod.get absks kscurd = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
                                      vsize, vstatus, vintst) ->
   voff = Int.shru vpaddr (Int.repr 12) ->
   rv_paddr <> Vint32 voff ->
   absinfer sch 
            (<||get_ksdom_paddr (| rv_paddr :: nil |) ;; 
                 s ||> ** HKsCurDomain kscurd ** HKsDomains absks ** P)
            (<|| ABORT ||> **
             HKsCurDomain kscurd ** HKsDomains absks ** P).
Proof.
intros.
subst.
assert (Hc: can_change_aop
            (HKsCurDomain kscurd ** HKsDomains absks ** P)) by
        can_change_aop_solver.
eapply absinfer_trans;
[ idtac |
  eapply absinfer_seq_abt;[ | | eauto]; try eauto].
eapply absinfer_seq; try eauto.
eapply absinfer_abt; eauto.
absimp_abt_solver.
instantiate(2:= get_rtsk_raddr (|rv_paddr :: nil|));
instantiate(2:= s0);
sep pauto.
Qed.

Lemma can_change_aop_Aarray_rm:
forall vl n m t l, can_change_aop (Aarray_rm l n t vl m).
Proof.
induction vl; induction n; induction m; intros; destruct l;
try can_change_aop_solver.
simpl; try can_change_aop_solver.
simpl.
split; auto.
Qed.

Hint Resolve  can_change_aop_Aarray_rm: can_change_aop.  

Lemma array_rm_update_eq_frm: 
  forall s b i vl v vi n m t P,
    (m < n)%nat -> 
    nth_val m vl = Some vi -> 
    s |= Aarray_rm (b,i) n t vl m ** P -> 
    s |= Aarray_rm (b,i) n t (update_nth_val m vl v) m ** P.
Proof.
  intros.
  sep cancel P.
  eapply array_rm_update_eq; eauto.
Qed.

Lemma val_inj_eq
: forall i0 a: int32,
    val_inj
      (notint
         (val_inj
            (if Int.eq i0  a
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
    val_inj
      (notint
         (val_inj
            (if Int.eq i0  a
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)))) = Vnull ->
    i0 = a.
Proof.
  intros.
  destruct H; intros.
  int auto.
  apply unsigned_inj; auto.
  int auto.
Qed.

Lemma get_set_struct_equal:
forall q1 t evstructs x x',
  Get_struct evstructs q1 = Some (q1, t, x) ->
  Get_struct (Set_struct evstructs q1 t x') q1 = Some (q1, t, x').
Proof.
  intros.
  induction evstructs.
  tryfalse.
  unfold Set_struct.
  destruct a. destruct p.
  destruct (os_inv.beq_addrval a q1) eqn:eq.
  destruct (type_eq t0 t) eqn:eq1.
  unfold Get_struct.
  destruct (os_inv.beq_addrval a q1) eqn:eq2.
  eapply type_eq_true_eq in eq1; subst; auto.
  tryfalse.
(*   eq1 : type_eq t0 t = false *)
  eapply beq_tid_true_eq in eq; subst.
  fold Set_struct.
  unfold Get_struct in H.
  rewrite beq_tid_true in H.
  inverts H.
  eapply type_eq_false_neq in eq1; tryfalse.
(* eq : beq_addrval a q1 = false *)
  fold Set_struct.
  assert (Get_struct evstructs q1 = Some (q1, t, x)).
  { unfold Get_struct in H.
    rewrite eq in H.
    fold Get_struct in H; auto.
  }
  unfold Get_struct.
  rewrite eq.
  fold Get_struct.
  eapply IHevstructs; auto.
Qed.

Definition init_mpax_if (vl:vallist) := 
match vl with
| (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
  (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: 
  rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil
 =>
( ksCurDomain_err (|nil|) ??
       ((*index = MPAXSHIPARTIONSTKCUR *)
        get_rtsk_baddr (|rv_baddr :: nil|) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxh ;;

        set_mpaxh (|(Vptr lses_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxh ;;
        get_rtsk_raddr (|rv_raddr :: nil|) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxl ;;
        (*index = MPAXSHIPARTIONCUR *)
        get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
      
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        get_ksdom_paddr (| rv_paddr :: nil |) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl)
       );; (* end of ksCurDomain <> -1*)
       (* index = MPAXSHAREDAREA *)
       set_mpaxh (|(Vptr lmpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxl ;;
       (* index = MPAXALLAREA *)
       set_mpaxh (|(Vptr lmpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXALLAREA))lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXALLAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxl ;;
       csl_xmc_clearFault ;;
       csl_cgem_clearMDMAError
  | _ => spec_abort
  end.

Definition init_mpax_after_if (vl:vallist) := 
match vl with
| (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
  (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: 
  rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil
 =>
set_mpaxh (|(Vptr lmpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxl ;;
       (* index = MPAXALLAREA *)
       set_mpaxh (|(Vptr lmpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXALLAREA))lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXALLAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxl ;;
       csl_xmc_clearFault ;;
       csl_cgem_clearMDMAError
| _ => spec_abort
end.


Lemma initMPAX_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal initMPAX vl logicl initMPAXPre ct->
    Some r =
    BuildRetI os_internal initMPAX vl logicl initMPAXPost ct->
    exists t d1 d2 s,
      os_internal initMPAX = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
  subst.
  rename v' into vidx.
  rename v'0 into vpaddr.
  rename v'1 into vaddr.
  rename v'2 into corenum.
  rename v'3 into vsize.
  rename v'4 into visr.
  rename v'5 into vie.
  rename v'6 into vis.
  rename v'7 into vier.
  rename v'8 into vcs.
  rename v'9 into xmpax.
  rename v'10 into sms_mpax.
  rename v'11 into ses_mpax.
  rename v'12 into xmpaxvl.
  rename v'13 into sms_mpaxvl.
  rename v'14 into ses_mpaxvl.
  rename v'15 into evstructs.
  rename v'34 into vcurd.
  rename v'35 into ksdom.
  rename v'36 into absks.
  rename v'37 into rtsk_vll.
  rename v'38 into absrtsk.
  match goal with
   H: ptr_no_dup ((Vptr ?v1) :: (Vptr ?v2) :: (Vptr ?v3) :: (Vptr ?v4) :: (Vptr ?v5) :: (Vptr ?v6) :: nil) |- _ =>
  rename v1 into lmpaxh; rename v2 into lmpaxl; rename v3 into lses_mpaxh;
  rename v4 into lses_mpaxl; rename v5 into lsms_mpaxh; rename v6 into lsms_mpaxl;
  rename H into Hno_dup
  end.
  hoare_lifts_trms_pre Aop.
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  <|| spec_code_cons' (initMPAX' (_ ++ (?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: _))) ?s1 ||> ** _ }} _ {{ _ }} => 
  rename v1 into rv_baddr; rename v2 into rv_raddr; rename v3 into rv_size;
  rename v4 into rv_vaddr; rename v5 into rv_paddr; rename s1 into s
  end.
  simpljoin.
(* os_initMPAX.index ′ =ₑ ′ 0;ₛ *)
  hoare forward.
(* os_initMPAX.paddress ′ =ₑ ′ 0;ₛ *)
  hoare forward.
(* os_initMPAX.vaddress ′ =ₑ ′ 0;ₛ *)
  hoare forward.
(* os_initMPAX.segSize ′ =ₑ ′ 0;ₛ *)
  hoare forward.
(* os_code_defs.corenum ′ =ₑ ′ DNUM;ₛ *)
  hoare forward.
(* initDefaultMPAX (­mpaxl ′, sms_mpaxl ′, ses_mpaxl ′­);ₛ *)
  hoare forward; eauto.
(*   unfold spec_code_cons in *. *)
  sep cancel AXMpax.
  sep cancel ASMSMpax.
  sep cancel ASESMpax.
  go.
(*   good_frm_sovler. *)
  unfold ptr_no_dup in Hno_dup.
  splits.
  eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); eauto.
  eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); eauto.
  pure_auto.
  intros.
  sep auto.
  intros.
  sep auto.
  hoare unfold.
  repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
  rename v'0 into visr.
  rename v'1 into vie.
  rename v'2 into vis.
  rename v'3 into vier.
  rename v'4 into vcs.
  rename v'5 into xmpax'.
  rename v'6 into sms_mpax'.
  rename v'7 into ses_mpax'.
  rename v'8 into xmpaxvl'.
  rename v'9 into sms_mpaxvl'.
  rename v'10 into ses_mpaxvl'.
  rename v'11 into evstructs.
  rename v'15 into lmpaxl.
  rename v'22 into lsms_mpaxl.
  rename v'23 into lses_mpaxl.
  rename v'27 into xmpaxl'.
  rename v'28 into smsmpaxl'.
  rename v'29 into sesmpaxl'.
  hoare unfold.
  unfold AKsCurDomain.
  unfold AKsDomains.
  hoare unfold.
  destruct v' as (dom_b, dom_i).
  match goal with H: length _ = ∘ DOMAIN_SIZE |- _ => rename H into Hdom_len end.
  match goal with H: _ <= Int.unsigned vcurd < _ \/ _ |- _ => rename H into Hcurd_rgn end.
  hoare_lifts_trms_pre (Aop, segSize, vaddress,
                        paddress, os_code_defs.index, 
                        Aisr, Aie, Ais, Acs, Aier,
                        AXMpax, ASMSMpax,ASESMpax,
                        AEvStructHeap, evstructheap).
  hoare remember (1::2::3::4::5::6::7::8::9::10
                  ::11::12::13::14::15::nil)%list pre.
   eapply seq_rule
     with (p':= (
   EX vsegsize vaddr vpaddr vidx xmpaxvl xmpax sms_mpaxvl sms_mpax 
      ses_mpaxvl ses_mpax evstructs vl0 vl1 vl2 vl3 vl4 vl5 s0,
   <|| s0 ||>  **
  LV segSize @ char_t |-> (Vint32 vsegsize) **
  LV vaddress @ long |-> (Vint32 vaddr) **
  LV paddress @ long |-> (Vint32 vpaddr) **
  LV os_code_defs.index @ long |-> (Vint32 vidx) **
  Aisr visr **
  Aie vie **
  Ais vis **
  Acs vcs **
  Aier vier **
  AXMpax xmpaxvl xmpax **
  ASMSMpax sms_mpaxvl sms_mpax **
  ASESMpax ses_mpaxvl ses_mpax **
  AEvStructHeap evstructs **
  HEvStructHeap evstructs ** 
  [| Get_struct evstructs lmpaxh = Some (lmpaxh, XMC_XMPAXH, vl0) /\ struct_type_vallist_match XMC_XMPAXH vl0 |] **
  [| Get_struct evstructs lmpaxl = Some (lmpaxl, XMC_XMPAXL, vl1) /\ struct_type_vallist_match XMC_XMPAXL vl1 |] **
  [| Get_struct evstructs lsms_mpaxh = Some (lsms_mpaxh, MSMC_SMSMPAXH, vl2) /\ struct_type_vallist_match MSMC_SMSMPAXH vl2 |] **
  [| Get_struct evstructs lsms_mpaxl = Some (lsms_mpaxl, MSMC_SMSMPAXL, vl3) /\ struct_type_vallist_match MSMC_SMSMPAXL vl3 |] **
  [| Get_struct evstructs lses_mpaxh = Some (lses_mpaxh, MSMC_SESMPAXH, vl4) /\ struct_type_vallist_match MSMC_SESMPAXH vl4 |] **
  [| Get_struct evstructs lses_mpaxl = Some (lses_mpaxl, MSMC_SESMPAXL, vl5) /\ struct_type_vallist_match MSMC_SESMPAXL vl5 |] **
  H11 **
  [| s0 = if Int.eq vcurd Int.mone
          then (spec_code_cons'
      (init_mpax_if ((Vptr lmpaxh
         :: Vptr lmpaxl
            :: Vptr lses_mpaxh
               :: Vptr lses_mpaxl :: Vptr lsms_mpaxh :: Vptr lsms_mpaxl :: nil) ++
        rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil)) s)
          else (spec_code_cons'
      (init_mpax_after_if ((Vptr lmpaxh
         :: Vptr lmpaxl
            :: Vptr lses_mpaxh
               :: Vptr lses_mpaxl :: Vptr lsms_mpaxh :: Vptr lsms_mpaxl :: nil) ++
        rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil)) s) |] )).
  eapply forward_rule1.
  introv Hsat.
  eapply adisj_elim in Hsat; destruct Hsat; eauto.
(*   If (ksCurDomain ′ !=ₑ ′ (-1)) *)
  hoare forward.
  pure_auto.
  pure_auto.
  2:{ match goal with H : _ |= _ |- _ => rename H into Hsat end.
      change ($ -1) with Int.mone in *.
      destruct Hsat as [Hsat | Hsat].
      sep split in Hsat.
      simpljoin.
      match goal with H:val_inj _ <> Vint32 Int.zero |- _ => rename H into Hval end.
      eapply notint_neq_zero_eq in Hval.
      left; rewrite Hval; eauto.
      sep_lifts_trms_in Hsat val_inj.
      eapply sep_pure_split in Hsat.
      simpljoin.
      match goal with H : _ |= _ |- _ => rename H into Hsat end.
      match goal with H:val_inj _ = Vint32 Int.zero \/ val_inj _ = Vnull
      |- _ => rename H into Hval end.
      eapply val_inj_eq in Hval.
      assert (Heq: Int.eq vcurd Int.mone = true).
      { rewrite Hval; auto. }
      right; rewrite Heq.
      simpl spec_code_cons'. simpl init_mpax_if.
      sep eexists.
      sep pauto.
      splits; eauto.
      eapply get_set_struct_equal; eauto.
      repeat try rewrite get_set_struct_notequal; eauto.
      eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); eauto.
      eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); eauto.
      splits; eauto.
      repeat try rewrite get_set_struct_notequal; eauto.
      eapply Hno_dup with (i:= 1%nat) (j:= 2%nat); eauto.
      eapply Hno_dup with (i:= 5%nat) (j:= 2%nat); eauto.
      eapply Hno_dup with (i:= 3%nat) (j:= 2%nat); eauto.
      unfold struct_type_vallist_match.
      unfold struct_type_vallist_match'.
      unfold rule_type_val_match.
      rewrite mund_int_a2; eauto.
      splits; eauto.
      rewrite get_set_struct_notequal; eauto.
      eapply get_set_struct_equal; eauto.
      rewrite get_set_struct_notequal; eauto.
      eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); eauto.
      eapply Hno_dup with (i:= 3%nat) (j:= 5%nat); eauto.
      splits; eauto.
      repeat try rewrite get_set_struct_notequal; eauto.
      eapply Hno_dup with (i:= 1%nat) (j:= 4%nat); eauto.
      eapply Hno_dup with (i:= 5%nat) (j:= 4%nat); eauto.
      eapply Hno_dup with (i:= 3%nat) (j:= 4%nat); eauto.
      unfold struct_type_vallist_match.
      unfold struct_type_vallist_match'.
      unfold rule_type_val_match.
      rewrite mund_int_a2; eauto.
      splits; eauto.
      rewrite get_set_struct_notequal; eauto.
      rewrite get_set_struct_notequal; eauto.
      eapply get_set_struct_equal; eauto.
      eapply Hno_dup with (i:= 5%nat) (j:= 1%nat); eauto.
      eapply Hno_dup with (i:= 3%nat) (j:= 1%nat); eauto.
      splits; eauto.
      repeat try rewrite get_set_struct_notequal; eauto.
      eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); eauto.
      eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); eauto.
      eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); eauto.
      unfold struct_type_vallist_match.
      unfold struct_type_vallist_match'.
      unfold rule_type_val_match.
      rewrite mund_int_a2; eauto.
  }
  subst H11.
  hoare_lifts_trms_pre val_inj.
  eapply pure_split_rule'; introv Hval_inj.
  change ($ -1) with Int.mone in *.
  destruct (Int.eq vcurd Int.mone) eqn: eq1; simpl in Hval_inj;
  try change (Int.notbool Int.one) with Int.zero in Hval_inj; destruct Hval_inj; tryfalse.
  eapply sem_lab.semacc_int_eq_false in eq1.
  hoare_lifts_trms_pre (Aop, kscurdom).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_cdom_cons; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* os_code_defs.index ′ =ₑ ′ MPAXSHIPARTIONSTKCUR;ₛ *)
  hoare forward.
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxh); eauto.
  repeat try rewrite get_set_struct_notequal; eauto.
  eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh1.
  apply ex_intro_rule; intro evh2.
  hoare_split_pure_all.
  destruct Hcurd_rgn as [Hcurd_rgn | Hf]; [idtac | subst; tryfalse].
  destruct Hcurd_rgn as (Hcurd_rgn1 & Hcurd_rgn2).
  (* unfold AKsDomains' *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat AKsDomains'.
  eapply AKsDomains'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned vcurd)); eauto.
  rewrite Hdom_len.
  unfold nat_of_Z in *.
  solve_part_int_rgn.
  unfold node_offt.
  hoare normal pre.
  apply ex_intro_rule; intro dom_vll1.
  apply ex_intro_rule; intro dom_vll2.
  apply ex_intro_rule; intro dom_vl.
  apply ex_intro_rule; intro int_vl.
  apply ex_intro_rule; intro dom_lb.
  apply ex_intro_rule; intro dom_li.
  apply ex_intro_rule; intro int_addr.
  hoare_split_pure_all.
  match goal with H: Vptr _ = Vptr _ /\ _ |- _ => destruct H as (Hptr & Hdom_mat); inverts Hptr end.
  lets Hdom_mat': Hdom_mat.
  lets Hdom_vl: struct_type_vallist_match_elim_9 Hdom_mat.
  simpljoin.
  simpl in Hdom_mat'.
  simpljoin.
  repeat try(match goal with
     H: match ?x with
           | Vint32 _ => _
           | _ => _
          end = true |- _ =>
     destruct x; tryfalse end).
  match goal with H: struct_type_vallist_match os_ucos_h.domain_t (_ :: Vint32 ?v :: _) |- _ => rename v into domid end.
  match goal with H: KsDomains_Good _ |- _ => rename H into Hdom_good end.
  match goal with H: _ = Z.to_nat (Int.unsigned vcurd) |- _ => rename H into Hvcurd_len end.
  assert (Hdomid_rgn: 0 <= Int.unsigned domid < PARTITION_NUM).
  {
  lets Hdomid_rgn: Hdom_good.
  clear -Hvcurd_len Hdomid_rgn Hcurd_rgn1 Hcurd_rgn2.
  destruct Hdomid_rgn as (_ & _ & Hdomid_rgn & _).
  specialize (Hdomid_rgn (Int.unsigned vcurd)).
  unfold nat_of_Z in Hdomid_rgn.
  rewrite <- Hvcurd_len in Hdomid_rgn.
  rewrite nth_error_middle in Hdomid_rgn.
  destruct Hdomid_rgn.
  split; solve_part_int_rgn.
  simpljoin.
  inverts H.
  inverts H0.
  auto.
  Optimize Proof.
  Optimize Heap.
  }
  destruct Hdomid_rgn as (Hdomid_pos & Hdomid_rgn).
  (* unfold RootTaskStk *)
  unfold ARootTaskStk.
  hoare_lifts_trms_pre ARootTaskStk'.
  hoare_assert_pure (length rtsk_vll = ∘ PARTITION_NUM).
  { match goal with H: _ |= _ |- _ => eapply ARootTaskStk'_len_frm in H; eauto end. }
  eapply pure_split_rule'; introv Hrtsk_vll_len.
  eapply backward_rule1.
  introv Hsat.
  eapply ARootTaskStk'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned domid)); eauto.
  rewrite Hrtsk_vll_len.
  unfold nat_of_Z.
  solve_part_int_rgn.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  (* mpaxh ′ → os_code_defs.mpaxh_segSize =ₑ ′ 12;ₛ *)
  hoare forward.
  (* mpaxh ′ → os_code_defs.mpaxh_bAddr =ₑ
  〈 long 〉 (&ₐ RootTaskStk ′ [(ksDomains ′ [ksCurDomain ′]) .. dom_t_ID]) ≫ ′ 12;ₛ *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  eapply cast_rv_ptr_to_int32.
  eapply addrof_array_elem_rv.
  sep get rv.
  sep_get_rv_array_struct_gen.
  auto.
  eauto.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  match goal with H: AKsDomains_P _ _ _ |- _ => rename H into Habsks end.
  lets Habsks': Habsks.
  eapply AKsDomains_P_split' in Habsks'.
  2:{ rewrite Hvcurd_len; unfold nat_of_Z in *; solve_part_int_rgn. }
  destruct Habsks' as (abs1 & abs2 & abs & abs' & idx & Hidx & Habsdom_l & Habsdom_r & Hcurdom & Hj & Hjall).
  subst idx.
  rewrite Int.add_zero_l in *.
  simpl in Hcurdom.
  simpljoin.
  match goal with H: KsDomsMod.join _ empenv _ |- _ =>
  eapply KsDomsMod.join_comm in H;
  eapply KsDomsMod.join_emp_eq in H; inverts H end.
  destruct abs as [[[[[[[[]]]]]]]].
  match goal with H: RHL_domain_P _ _ |- _ => destruct H as (Hrhl_dom & Hrhl_int) end.
  funfold Hrhl_dom.
  rename d0 into domid.
  lets Hget_dom: KsDomsMod.join_sig_get Hj.
  lets Hget_dom': KsDomsMod.join_get_r Hjall Hget_dom.
  rewrite Hvcurd_len in Hget_dom, Hget_dom'.
  rewrite Z2Nat.id in Hget_dom, Hget_dom'; auto with zarith.
  rewrite Int.repr_unsigned in Hget_dom, Hget_dom'.
  match goal with H: RootTaskStk_head = (?vb, ?vi) |- _ =>
   rename H into Htsk_addr; rename vb into vtsk_b; rename vi into vtsk_i end.
  remember (Tarray long ∘ (2 * PTHREAD_STACK_MIN / 4)) as tp.
  remember ((ptr_to_int32 (vtsk_b, vtsk_i +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned domid) * typelen tp)))>>ᵢ $ 12) as voff.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, kscurdom, ksdoms).
  assert (Hrv_baddr: rv_baddr <> Vint32 voff \/ rv_baddr = Vint32 voff) by tauto.
  destruct Hrv_baddr as [ Habt | Hrv_baddr].
  { eapply abscsq_rule.
     apply noabs_oslinv.
     eapply initmpax_absimp_get_rtsk_baddr_abt; eauto.
     can_change_aop_solver.
     apply absinfer_eq.
     apply absabort_rule.
  }
  subst rv_baddr.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_get_rtsk_baddr; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  repeat try rewrite get_set_struct_notequal; eauto.
  eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); eauto.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Astruct lmpaxh).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Astruct lmpaxh _  (Vint32 ?v :: _) ** _ }} _ {{ _ }} =>
  assert (Hvoff_eq: voff = v)
  end.
  { substs.
     simpl.
     erewrite Int_mul_eq.
     auto with zarith.
     solve_part_int_rgn.
     clear. solve_part_int_rgn.
  }
  unfold AXMpax.
  hoare_lifts_trms_pre (RH_XMpax_P, R_XMpax_P).
  apply pure_split_rule'; introv Hrh_xmpax.
  apply pure_split_rule'; introv Hr_xmpax.
  assert (Hget_xmpax:  exists mpaxl mpaxh, get xmpax' ($ MPAXSHIPARTIONSTKCUR) = Some (mpaxl, mpaxh)).
  { eapply Hrh_xmpax; unfold MPAXSHIPARTIONSTKCUR.
     change ( Int.unsigned ($ 7)) with 7; auto with zarith.
  }
  destruct Hget_xmpax as (abs_mpaxl & abs_mpaxh & Hget_xmpax).
  (* CSL_XMC_setXMPAXH (os_code_defs.index ′, mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  hoare_assert_pure (length xmpaxvl' = 32)%nat.
  { unfold Axmpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_xmpax.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_mpax: Hget_xmpax.
  eapply Hr_xmpax in Heq_mpax.
  destruct Heq_mpax as (Heq_xl & Heq_xh).
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  lets Heq_xl': Heq_xl; lets Heq_xh': Heq_xh.
  eapply nth_val_nth_val'_some_eq in Heq_xl, Heq_xh.
  rewrite Heq_xh.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXH_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hvoff_eq.
         split.
         rewrite H26.
         eapply Get_struct_Set_vl; eauto.
         eapply get_struct_vl'; auto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
     update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)) xmpaxvl' v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  unfold PTHREAD_STACK_MIN in *.
  rewrite Hvoff_eq in *.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq1: vll = vll')
  end.
  { rewrite H26. 
    eapply set_struct_update_vl_gen; eauto.
     eapply get_struct_vl'; auto. }
  (* end of assign xmpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': evt_spec_defs.Get_struct _ lsms_mpaxh = Some (lsms_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsh: evt_spec_defs.Get_struct (Set_struct vll q tp vl' )  lsms_mpaxh
                                         = Some (lsms_mpaxh, tp', vl''))
  end.
  { try repeat rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 4%nat); simpl; eauto. 
     eapply Hno_dup with (i:= 5%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 4%nat); simpl; eauto. 
     eapply Hno_dup with (i:= 0%nat) (j:= 4%nat); simpl; eauto.  }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxh); eauto.
  rewrite <- Hset_eq1; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh3.
  apply ex_intro_rule; intro evh4.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq1_conv end.
  (* sms_mpaxh′→smsmpaxh_segSz  =ₑ ′12 ;ₛ  *)
  hoare forward.
  (* sms_mpaxh′→smsmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12 ;ₛ  *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  eapply cast_rv_ptr_to_int32.
  eapply addrof_array_elem_rv.
  sep get rv.
  sep_get_rv_array_struct_gen.
  auto.
  Optimize Proof.
  Optimize Heap.
  eauto.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.

  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASMSMpax*)
  unfold ASMSMpax.
  hoare_lifts_trms_pre (RH_SMS_Mpax_P, R_SMS_Mpax_P).
  apply pure_split_rule'; introv Hrh_sms.
  apply pure_split_rule'; introv Hr_sms.
  assert (Hget_sms:  exists mpaxl mpaxh, get sms_mpax' ($ MPAXSHIPARTIONSTKCUR) = Some (mpaxl, mpaxh)).
  { eapply Hrh_sms; unfold MPAXSHIPARTIONSTKCUR.
     change ( Int.unsigned ($ 7)) with 7; auto with zarith.
  }
  destruct Hget_sms as (abs_smsl & abs_smsh & Hget_sms).
  (* CSL_MSMC_setSMSMPAXH (coreNum ′,os_code_defs.index ′,sms_mpaxh ′);ₛ *)
  (* unfold ASMSMpax *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  hoare_assert_pure (length sms_mpaxvl' = 16)%nat.
  { unfold Asms_mpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_sms.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_mpax: Hget_sms.
  eapply Hr_sms in Heq_mpax.
  destruct Heq_mpax as (Heq_smsl & Heq_smsh).
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  lets Heq_smsl': Heq_smsl; lets Heq_smsh': Heq_smsh.
  eapply nth_val_nth_val'_some_eq in Heq_smsl, Heq_smsh.
  rewrite Heq_smsh.
  hoare_split_pure_all.
  assert (Heq_dnum: Z.of_nat (Z.to_nat DNUM) = DNUM).
  { pose proof dnum_range.
     auto with zarith. }
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq1 in *. rewrite Hset_eq1_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)) sms_mpaxvl' v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq2: vll = vll')
  end.
  { rewrite Hset_eq1 in *. rewrite Hset_eq1_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': evt_spec_defs.Get_struct _ lses_mpaxh = Some (lses_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesh: evt_spec_defs.Get_struct (Set_struct vll q tp vl' )  lses_mpaxh
                                         = Some (lses_mpaxh, tp', vl''))
  end.
  { try repeat rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 2%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxh); eauto.
  rewrite <- Hset_eq2; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh5.
  apply ex_intro_rule; intro evh6.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq2_conv end.
  (* ses_mpaxh′→sesmpaxh_segSz  =ₑ ′12 ;ₛ  *)
  hoare forward.
  (* ses_mpaxh′→sesmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12 ;ₛ  *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  eapply cast_rv_ptr_to_int32.
  eapply addrof_array_elem_rv.
  sep get rv.
  sep_get_rv_array_struct_gen.
  auto.
  eauto.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASESMpax*)
  unfold ASESMpax.
  hoare_lifts_trms_pre (RH_SES_Mpax_P, R_SES_Mpax_P).
  apply pure_split_rule'; introv Hrh_ses.
  apply pure_split_rule'; introv Hr_ses.
  assert (Hget_ses:  exists mpaxl mpaxh, get ses_mpax' ($ MPAXSHIPARTIONSTKCUR) = Some (mpaxl, mpaxh)).
  { eapply Hrh_ses; unfold MPAXSHIPARTIONSTKCUR.
     change ( Int.unsigned ($ 7)) with 7; auto with zarith.
  }
  destruct Hget_ses as (abs_sesl & abs_sesh & Hget_ses).
  (* CSL_MSMC_setSESMPAXH (coreNum ′,os_code_defs.index ′,ses_mpaxh ′);ₛ *)
  (* unfold ASESMpax *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  hoare_assert_pure (length ses_mpaxvl' = 16)%nat.
  { unfold Ases_mpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_ses.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_mpax: Hget_ses.
  eapply Hr_ses in Heq_mpax.
  destruct Heq_mpax as (Heq_sesl & Heq_sesh).
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  lets Heq_sesl': Heq_sesl; lets Heq_sesh': Heq_sesh.
  eapply nth_val_nth_val'_some_eq in Heq_sesl, Heq_sesh.
  rewrite Heq_sesh.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq2 in *. rewrite Hset_eq2_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)) ses_mpaxvl' v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq3: vll = vll')
  end.
  { rewrite Hset_eq2 in *. rewrite Hset_eq2_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpax *)
  assert 
  (Hgst_xmpax:
     evt_spec_defs.Get_struct
       (Set_struct
          (Set_struct
             (Set_struct evstructs lmpaxl XMC_XMPAXL
                (get_mpax_struct xmpaxl'
                   (xmc_raddr
                    :: xmc_sr
                       :: xmc_sw
                          :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)))
             lsms_mpaxl MSMC_SMSMPAXL
             (get_mpax_struct smsmpaxl'
                (smsl_raddr
                 :: smsl_sr
                    :: smsl_sw
                       :: smsl_sx
                          :: smsl_ur :: smsl_uw :: smsl_ux :: nil)))
          lses_mpaxl MSMC_SESMPAXL
          (get_mpax_struct sesmpaxl'
             (sesl_raddr
              :: sesl_sr
                 :: sesl_sw
                    :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))) lmpaxl = Some (lmpaxl, XMC_XMPAXL,
                (get_mpax_struct xmpaxl'
                   (xmc_raddr
                    :: xmc_sr
                       :: xmc_sw
                          :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)))).
  {  
     rewrite get_set_struct_notequal; eauto.
     rewrite get_set_struct_notequal; eauto.
     eapply get_set_struct_equal; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 1%nat); simpl; eauto.
  }
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': evt_spec_defs.Get_struct _ lmpaxl = Some (lmpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxl: evt_spec_defs.Get_struct (Set_struct vll q tp vl' )  lmpaxl
                                         = Some (lmpaxl, tp', vl''))
  end.
  {  rewrite get_set_struct_notequal; eauto.
     rewrite get_set_struct_notequal; eauto.
     rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 1%nat); simpl; eauto. }
  (* paddress ′ =ₑ
  〈 long 〉 (&ₐ RootTaskStk ′ [(ksDomains ′ [ksCurDomain ′]) .. dom_t_ID]);ₛ *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar;
                  [ intro s_; split; intro Hsat; try sep pauto
                  | idtac
                  | apply assign_type_match_true; simpl; auto | li_sepauto li].
  introv Hsat.
  eapply cast_rv_ptr_to_int32.
  eapply addrof_array_elem_rv.
  sep get rv.
  sep_get_rv_array_struct_gen.
  auto.
  Optimize Proof.
  Optimize Heap.
  eauto.
  simpl; auto.
  (*
  IF (paddress ′ ≥ ′ 2147483648)
  {paddress ′ =ₑ paddress ′ − ′ 2147483648 ≫ ′ 12 |ₑ ′ 8388608}
  ELSE {paddress ′ =ₑ paddress ′ ≫ ′ 12};ₛ
  *)
  hoare_lifts_trms_pre (paddress).
  hoare remember (1:: nil)%nat pre.
  erewrite <- Int_mul_eq with (n:= (typelen (Tarray long ∘ (2 * 4096 / 4)))).
  2:{ solve_part_int_rgn. }
  2:{ clear. unfold nat_of_Z. unfold typelen. solve_part_int_rgn. }
  match goal with H: Int.shru ?v1 ?x = Int.shru ?v2 ?x |- _ =>
  assert (Hvoff_eq': v1 = v2)
  end.
  { unfold nat_of_Z.
     unfold typelen.
     change (8192) with (Z.of_nat (Z.to_nat 8192)).
     rewrite <- Int_mul_eq.
     unfold ptr_to_int32. auto with zarith.
     solve_part_int_rgn.
     clear; solve_part_int_rgn.
  }
  rewrite Hvoff_eq'.
  eapply seq_rule.
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  LV paddress @ Tint32  |-> Vint32 ?vpaddr ** ?P }} _ {{ _ }} =>
  instantiate(1:= (LV paddress @ long
    |-> Vint32 ((if Int.ltu vpaddr (Int.repr (0x80000000))
                             then Int.shru vpaddr (Int.repr 12)
                             else Int.or (Int.shru (Int.sub vpaddr (Int.repr (0x80000000))) (Int.repr 12))
                                                  (Int.repr (0x800000)))) **
    P)); subst P
  end.
  (* IF (paddress ′ ≥ ′ 2147483648) *)
  hoare forward.
  pure_auto.
  pure_auto.
  pure_auto.
  (*  paddress ′ =ₑ paddress ′ − ′ 2147483648 ≫ ′ 12 |ₑ ′ 8388608  *)
  hoare forward.
  (* paddress ′ =ₑ paddress ′ ≫ ′ 12 *)
  hoare forward.
  match goal with H: _ |= _ |- _ => rename H into Hsat end.
  clear -Hsat.
  destruct Hsat as [Hsat | Hsat];
  sep pauto;
  clear Hsat;
  change (Int.ltu ($ 12) Int.iwordsize) with true in *;
  simpl val_inj in *;
  destruct (Int.ltu ($ 2147483648)
                  (Int.or ($ Z.pos vtsk_b<<ᵢ$ offset_bit)
                     (Int.zero_ext offset_bit
                        (vtsk_i +ᵢ  Int.mul ($ 8192) domid)))) eqn: eq1;
  destruct (Int.eq
                  (Int.or ($ Z.pos vtsk_b<<ᵢ$ offset_bit)
                     (Int.zero_ext offset_bit
                        (vtsk_i +ᵢ  Int.mul ($ 8192) domid))) 
                  ($ 2147483648)) eqn: eq2;
  destruct ( Int.ltu
                        (Int.or ($ Z.pos vtsk_b<<ᵢ$ offset_bit)
                           (Int.zero_ext offset_bit (vtsk_i +ᵢ  Int.mul ($ 8192) domid)))
                        ($ 2147483648)) eqn:eq3;
  simpl val_inj in *;
  try change (Int.ltu Int.zero Int.one) with true in *;
  try change (Int.ltu Int.one Int.zero) with false in *; 
  simpl val_inj in *;
  try rewrite Intlt_false_is_Zge in eq1;
  try rewrite Intlt_true_is_Zlt in eq1;
  try rewrite Intlt_false_is_Zge in eq3;
  try rewrite Intlt_true_is_Zlt in eq3;
  try (rewrite Inteq_true_is_Zeq in eq2; try rewrite eq2 in eq1);
  try rewrite Inteq_false_is_Zneq in eq2;
  tryfalse; auto with zarith; try solve[false; auto with zarith].
  destruct H; tryfalse.
  destruct H; tryfalse.
  destruct H; tryfalse.
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  LV paddress @ Tint32  |-> Vint32 ?vpaddr ** ?P }} _ {{ _ }} =>
  subst P; remember vpaddr as voff'
  end.
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxl); eauto.
  rewrite <- Hset_eq3; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh7.
  apply ex_intro_rule; intro evh8.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq3_conv end.
  (* mpaxl′→mpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* mpaxl′→mpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_rAddr =ₑ paddress′;ₛ  *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, kscurdom, ksdoms).
  assert (Hrv_raddr: rv_raddr <> Vint32 voff' \/ rv_raddr = Vint32 voff') by tauto.
  destruct Hrv_raddr as [ Habt | Hrv_raddr].
  { subst voff'.
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply initmpax_absimp_get_rtsk_raddr_abt; eauto.
     can_change_aop_solver.
     unfold PTHREAD_STACK_MIN. rewrite Hvoff_eq'. auto.
     apply absinfer_eq.
     apply absabort_rule.
  }
  subst rv_raddr.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_get_rtsk_raddr; eauto.
  can_change_aop_solver.
  subst voff'.
  unfold PTHREAD_STACK_MIN. rewrite Hvoff_eq'. auto.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl0; remember (XmcMod.set abs idx v) as xmpax0;
  assert(Hget_xmpax0: get xmpax0 idx = Some v) by ( subst xmpax0; rewrite XmcMod.map_get_set; auto)
  end.
  (* CSL_XMC_setXMPAXL (os_code_defs.index ′, mpaxl ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax0: (length xmpaxvl0 = 32)%nat).
  { subst xmpaxvl0.
     rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_mpax: Hget_xmpax0.
  lets Heq_xl0: nth_upd_neqrev Heq_xl'; try erewrite <- Heqxmpaxvl0 in Heq_xl0.
  auto with zarith.
  lets Heq_xl0': nth_val_nth_val'_some_eq Heq_xl0.
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  rewrite Heq_xl0'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXL_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq3 in *. rewrite Hset_eq3_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXL _,
  H1: ?v1 = set_mpax_struct abs_mpaxl _ _,
  H2: ?v2 = XmcMod.set xmpax0 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqxmpaxvl0.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)) xmpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax0; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq4: vll = vll')
  end.
  { rewrite Hset_eq3 in *. rewrite Hset_eq3_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpaxl *)
  assert 
  (Hgst_smsmpax:
     Get_struct
       (Set_struct
          (Set_struct
             (Set_struct evstructs lmpaxl XMC_XMPAXL
                (get_mpax_struct xmpaxl'
                   (xmc_raddr
                    :: xmc_sr
                       :: xmc_sw
                          :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)))
             lsms_mpaxl MSMC_SMSMPAXL
             (get_mpax_struct smsmpaxl'
                (smsl_raddr
                 :: smsl_sr
                    :: smsl_sw
                       :: smsl_sx
                          :: smsl_ur :: smsl_uw :: smsl_ux :: nil)))
          lses_mpaxl MSMC_SESMPAXL
          (get_mpax_struct sesmpaxl'
             (sesl_raddr
              :: sesl_sr
                 :: sesl_sw
                    :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))) lsms_mpaxl = Some (lsms_mpaxl, MSMC_SMSMPAXL,
                (get_mpax_struct smsmpaxl'
                (smsl_raddr
                 :: smsl_sr
                    :: smsl_sw
                       :: smsl_sx
                          :: smsl_ur :: smsl_uw :: smsl_ux :: nil)))).
  {  
     rewrite get_set_struct_notequal; eauto.
     eapply get_set_struct_equal; eauto.
     rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 5%nat); simpl; eauto.
  }
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxl = Some (lsms_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsl: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxl
                                         = Some (lsms_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxl); eauto.
  rewrite <- Hset_eq4; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh9.
  apply ex_intro_rule; intro evh10.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq4_conv end.
  (* sms_mpaxl ′ → smsmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_raddr =ₑ paddress′;ₛ  *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  (* hoare_lifts_trms_pre (Aop, kscurdom, ksdoms). *)
  (* subst voff'.
  unfold PTHREAD_STACK_MIN. rewrite Hvoff_eq'. auto. *)
  (* apply absinfer_eq. *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl0; remember (SmsMod.set abs idx v) as sms_mpax0;
  assert(Hget_sms0: get sms_mpax0 idx = Some v) by ( subst sms_mpax0; rewrite SmsMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSMSMPAXL (coreNum ′, os_code_defs.index ′, sms_mpaxl ′);ₛ *)
  (* unfold SMSMPAX *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert (Hlen_sms0: (length sms_mpaxvl0 = 16)%nat).
  { subst sms_mpaxvl0.
     rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_sms: Hget_sms0.
  lets Heq_smsl0: nth_upd_neqrev Heq_smsl'; try erewrite <- Heqsms_mpaxvl0 in Heq_smsl0.
  auto with zarith.
  lets Heq_smsl0': nth_val_nth_val'_some_eq Heq_smsl0.
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  rewrite Heq_smsl0'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXL_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq4 in *. rewrite Hset_eq4_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXL _,
  H1: ?v1 = set_mpax_struct abs_smsl _ _,
  H2: ?v2 =  SmsMod.set sms_mpax0 _ _ |- _ =>
  destruct H0 as (Hget_set_smsl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqsms_mpaxvl0.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)) sms_mpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms0; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq5: vll = vll')
  end.
  { rewrite Hset_eq4 in *. rewrite Hset_eq4_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpaxl *)
  assert 
  (Hgst_sesmpax:
     Get_struct
       (Set_struct
          (Set_struct
             (Set_struct evstructs lmpaxl XMC_XMPAXL
                (get_mpax_struct xmpaxl'
                   (xmc_raddr
                    :: xmc_sr
                       :: xmc_sw
                          :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)))
             lsms_mpaxl MSMC_SMSMPAXL
             (get_mpax_struct smsmpaxl'
                (smsl_raddr
                 :: smsl_sr
                    :: smsl_sw
                       :: smsl_sx
                          :: smsl_ur :: smsl_uw :: smsl_ux :: nil)))
          lses_mpaxl MSMC_SESMPAXL
          (get_mpax_struct sesmpaxl'
             (sesl_raddr
              :: sesl_sr
                 :: sesl_sw
                    :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))) lses_mpaxl = Some (lses_mpaxl, MSMC_SESMPAXL,
                (get_mpax_struct sesmpaxl'
                (sesl_raddr
                 :: sesl_sr
                    :: sesl_sw
                       :: sesl_sx
                          :: sesl_ur :: sesl_uw :: sesl_ux :: nil)))).
  {  eapply get_set_struct_equal; eauto.
     rewrite get_set_struct_notequal; eauto.
     rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); simpl; eauto.
  }
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxl = Some (lses_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesl: Get_struct (Set_struct vll q tp vl' )  lses_mpaxl
                                         = Some (lses_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxl); eauto.
  rewrite <- Hset_eq5; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh11.
  apply ex_intro_rule; intro evh12.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq5_conv end.
  (* ses_mpaxl ′ → sesmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_raddr =ₑ paddress′;ₛ  *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl0; remember (SesMod.set abs idx v) as ses_mpax0;
  assert(Hget_ses0: get ses_mpax0 idx = Some v) by ( subst ses_mpax0; rewrite SesMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSESMPAXL (coreNum ′, os_code_defs.index ′, ses_mpaxl ′);ₛ *)
  (* unfold SMSMPAX *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert (Hlen_ses0: (length ses_mpaxvl0 = 16)%nat).
  { subst ses_mpaxvl0.
     rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONSTKCUR * 2))); eauto.
  unfold MPAXSHIPARTIONSTKCUR. auto with zarith.
  lets Heq_ses: Hget_ses0.
  lets Heq_sesl0: nth_upd_neqrev Heq_sesl'; try erewrite <- Heqses_mpaxvl0 in Heq_sesl0.
  auto with zarith.
  lets Heq_sesl0': nth_val_nth_val'_some_eq Heq_sesl0.
  unfold MPAXSHIPARTIONSTKCUR in *.
  change (Int.unsigned ($ 7)) with 7 in *.
  rewrite Heq_sesl0'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXL_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq5 in *. rewrite Hset_eq5_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXL _,
  H1: ?v1 = set_mpax_struct abs_sesl _ _,
  H2: ?v2 =  SesMod.set ses_mpax0 _ _ |- _ =>
  destruct H0 as (Hget_set_sesl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqses_mpaxvl0.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)) ses_mpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONSTKCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses0; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq6: vll = vll')
  end.
  { rewrite Hset_eq5 in *. rewrite Hset_eq5_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lmpaxh = Some (lmpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxh: Get_struct (Set_struct vll q tp vl' )  lmpaxh
                                         = Some (lmpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 4%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); simpl; eauto. }
  clear Hset_eq1 (* Hget_set_smsh *) Hset_eq1_conv 
        Hset_eq2 (* Hget_set_sesh *)  Hset_eq2_conv
        Hset_eq3 (* Hget_set_mpaxl *) Hset_eq3_conv (* Hget_set_mpaxl' *)
        Hset_eq4 (* Hget_set_smsl *) Hset_eq4_conv (* Hget_set_smsl' *)
        Hset_eq5 (* Hget_set_sesl *) Hset_eq5_conv (* Hget_set_sesl' *).
  (* os_code_defs.index ′ =ₑ ′ MPAXSHIPARTIONCUR;ₛ *)
  hoare forward.
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxh); eauto.
  rewrite <- Hset_eq6; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh1'.
  apply ex_intro_rule; intro evh2'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq6_conv end.
  (* mpaxh ′ → os_code_defs.mpaxh_segSize =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ  *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  sep_get_rv_array_struct_gen.
  simpl; auto.
  auto with zarith.
  (* mpaxh ′ → os_code_defs.mpaxh_bAddr =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  hoare_lifts_trms_pre (Astruct lmpaxh).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Astruct lmpaxh XMC_XMPAXH (Vint32 ?v1 :: Vint32 ?v2 :: nil) ** _ }} _ {{ _ }} => 
  remember v1 as lvaddr; remember v2 as rv_vsize
  end.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, kscurdom, ksdoms).
  assert (Hrv_size_vaddr: ~(rv_size = Vint32 rv_vsize /\ rv_vaddr = Vint32 lvaddr)
                                                 \/ (rv_size = Vint32 rv_vsize /\ rv_vaddr = Vint32 lvaddr)) by tauto.
  destruct Hrv_size_vaddr as [ Habt | Hrv_size_vaddr].
  { eapply abscsq_rule.
     apply noabs_oslinv.
     eapply initmpax_absimp_get_ksdom_size_vaddr_abt; eauto.
     can_change_aop_solver.
     apply absinfer_eq.
     apply absabort_rule.
  }
  destruct Hrv_size_vaddr.
  subst rv_size; subst rv_vaddr.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_get_ksdom_size_vaddr; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl1; remember (XmcMod.set abs idx v) as xmpax1
  end.
  assert(Hget_xmpax1: exists mpaxl mpaxh,  get xmpax1 ($ MPAXSHIPARTIONCUR) = Some (mpaxl, mpaxh)).
  { subst xmpax1.
     do 2 try rewrite XmcMod.map_get_set'; auto.
     eapply Hrh_xmpax; unfold MPAXSHIPARTIONCUR.
     change ( Int.unsigned ($ 6)) with 6; auto with zarith.
  }
  destruct Hget_xmpax1 as (abs_mpaxl1 & abs_mpaxh1 & Hget_xmpax1).
  (* CSL_XMC_setXMPAXH (os_code_defs.index ′, mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax1: (length xmpaxvl1 = 32)%nat).
  { subst xmpaxvl1.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_mpax1: Hget_xmpax1.
  rewrite  Heqxmpax1 in Heq_mpax1.
  do 2 try rewrite XmcMod.map_get_set' in Heq_mpax1; auto.
  eapply Hr_xmpax in Heq_mpax1.
  destruct Heq_mpax1 as (Heq_xl1 & Heq_xh1).
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  do 2 try eapply nth_upd_neqrev in Heq_xl1;
  try erewrite <- Heqxmpaxvl1 in Heq_xl1; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_xh1;
  try erewrite <- Heqxmpaxvl1 in Heq_xh1; try solve [auto with zarith].
  lets Heq_xl1': Heq_xl1; lets Heq_xh1': Heq_xh1.
  eapply nth_val_nth_val'_some_eq in Heq_xl1, Heq_xh1.
  rewrite Heq_xh1.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXH_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq6 in *. rewrite Hset_eq6_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXH _,
  H1: ?v1 = set_mpax_struct abs_mpaxh1 _ _,
  H2: ?v2 = XmcMod.set xmpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqxmpaxvl1.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)) xmpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONSTKCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  unfold MPAXSHIPARTIONCUR in *.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  unfold MPAXSHIPARTIONCUR in *; auto with zarith.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq7: vll = vll')
  end.
  { rewrite Hset_eq6 in *. rewrite Hset_eq6_conv in *.
    eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxh = Some (lsms_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsh1: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxh
                                         = Some (lsms_mpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 2%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 4%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxh); eauto.
  rewrite <- Hset_eq7; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh3'.
  apply ex_intro_rule; intro evh4'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq7_conv end.
  (* sms_mpaxh′→smsmpaxh_segSz  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ  *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  sep_get_rv_array_struct_gen.
  simpl; auto.
  auto with zarith.
  (* sms_mpaxh′→smsmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ   *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASMSMpax*)
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl1; remember (SmsMod.set abs idx v) as sms_mpax1
  end.
  assert(Hget_sms1: exists mpaxl mpaxh,  get sms_mpax1 ($ MPAXSHIPARTIONCUR) = Some (mpaxl, mpaxh)).
  { subst sms_mpax1.
     do 2 try rewrite SmsMod.map_get_set'; auto.
     eapply Hrh_sms; unfold MPAXSHIPARTIONCUR.
     change ( Int.unsigned ($ 6)) with 6; auto with zarith.
  }
  destruct Hget_sms1 as (abs_smsl1 & abs_smsh1 & Hget_sms1).
  (* CSL_MSMC_setSMSMPAXH (coreNum ′,os_code_defs.index ′,sms_mpaxh ′);ₛ *)
  (* unfold ASMSMpax *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert(Hlen_sms1: (length sms_mpaxvl1 = 16)%nat).
  { subst sms_mpaxvl1.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_mpax1: Hget_sms1.
  rewrite  Heqsms_mpax1 in Heq_mpax1.
  do 2 try rewrite SmsMod.map_get_set' in Heq_mpax1; auto.
  eapply Hr_sms in Heq_mpax1.
  destruct Heq_mpax1 as (Heq_smsl1 & Heq_smsh1).
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  do 2 try eapply nth_upd_neqrev in Heq_smsl1;
  try erewrite <- Heqsms_mpaxvl1 in Heq_smsl1; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_smsh1;
  try erewrite <- Heqsms_mpaxvl1 in Heq_smsh1; try solve [auto with zarith].
  lets Heq_smsl1': Heq_smsl1; lets Heq_smsh1': Heq_smsh1.
  eapply nth_val_nth_val'_some_eq in Heq_smsl1, Heq_smsh1.
  rewrite Heq_smsh1.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq7 in *. rewrite Hset_eq7_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXH _,
  H1: ?v1 = set_mpax_struct abs_smsh1 _ _,
  H2: ?v2 =  SmsMod.set sms_mpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_smsh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqsms_mpaxvl1.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)) sms_mpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  unfold MPAXSHIPARTIONCUR in *.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq8: vll = vll')
  end.
  { rewrite Hset_eq7 in *. rewrite Hset_eq7_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxh = Some (lses_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesh1: Get_struct (Set_struct vll q tp vl' )  lses_mpaxh
                                         = Some (lses_mpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 1%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 2%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxh); eauto.
  rewrite <- Hset_eq8; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh5'.
  apply ex_intro_rule; intro evh6'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq8_conv end.
  (* ses_mpaxh′→sesmpaxh_segSz  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ   *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  sep_get_rv_array_struct_gen.
  simpl; auto.
  auto with zarith.
  (* ses_mpaxh′→sesmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ   *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASESMpax*)
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl1; remember (SesMod.set abs idx v) as ses_mpax1
  end.
  assert(Hget_ses1: exists mpaxl mpaxh,  get ses_mpax1 ($ MPAXSHIPARTIONCUR) = Some (mpaxl, mpaxh)).
  { subst ses_mpax1.
     do 2 try rewrite SesMod.map_get_set'; auto.
     eapply Hrh_ses; unfold MPAXSHIPARTIONCUR.
     change ( Int.unsigned ($ 6)) with 6; auto with zarith.
  }
  destruct Hget_ses1 as (abs_sesl1 & abs_sesh1 & Hget_ses1).
  (* CSL_MSMC_setSESMPAXH (coreNum ′,os_code_defs.index ′,ses_mpaxh ′);ₛ *)
  (* unfold ASESMpax *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert(Hlen_ses1: (length ses_mpaxvl1 = 16)%nat).
  { subst ses_mpaxvl1.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2 + 1))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_mpax1: Hget_ses1.
  rewrite  Heqses_mpax1 in Heq_mpax1.
  do 2 try rewrite SesMod.map_get_set' in Heq_mpax1; auto.
  eapply Hr_ses in Heq_mpax1.
  destruct Heq_mpax1 as (Heq_sesl1 & Heq_sesh1).
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  do 2 try eapply nth_upd_neqrev in Heq_sesl1;
  try erewrite <- Heqses_mpaxvl1 in Heq_sesl1; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_sesh1;
  try erewrite <- Heqses_mpaxvl1 in Heq_sesh1; try solve [auto with zarith].
  lets Heq_sesl1': Heq_sesl1; lets Heq_sesh1': Heq_sesh1.
  eapply nth_val_nth_val'_some_eq in Heq_sesl1, Heq_sesh1.
  rewrite Heq_sesh1.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq8 in *. rewrite Hset_eq8_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXH _,
  H1: ?v1 = set_mpax_struct abs_sesh1 _ _,
  H2: ?v2 =  SesMod.set ses_mpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_sesh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqses_mpaxvl1.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)) ses_mpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2 + 1)).
  sep eexists.
  unfold MPAXSHIPARTIONCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq9: vll = vll')
  end.
  { rewrite Hset_eq8 in *. rewrite Hset_eq8_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lmpaxl = Some (lmpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxl1: Get_struct (Set_struct vll q tp vl' )  lmpaxl
                                         = Some (lmpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 5%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 1%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxl); eauto.
  rewrite <- Hset_eq9; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh7'.
  apply ex_intro_rule; intro evh8'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq9_conv end.
  (* mpaxl′→mpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* mpaxl′→mpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl ′ → mpaxl_rAddr =ₑ
  (ksDomains ′ [ksCurDomain ′]) .. dom_t_pAddress ≫ ′ 12;ₛ *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  hoare_lifts_trms_pre (Astruct lmpaxl).
  match goal with 
  | |- {|_, _, _, _, _, _|} |-_ 
  {{ Astruct lmpaxl XMC_XMPAXL (Vint32 ?v1 :: _ :: _ :: _ :: _ :: _ :: _  :: nil) ** _ }} _ {{ _ }} =>
    remember v1 as voff1 
  end.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, kscurdom, ksdoms).
  assert (Hrv_paddr: rv_paddr <> Vint32 voff1 \/ rv_paddr = Vint32 voff1) by tauto.
  destruct Hrv_paddr as [ Habt | Hrv_paddr].
  { subst voff1.
     eapply abscsq_rule.
     apply noabs_oslinv.
     eapply initmpax_absimp_get_ksdom_paddr_abt; eauto.
     can_change_aop_solver.
     apply absinfer_eq.
     apply absabort_rule.
  }
  subst rv_paddr.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_get_ksdom_paddr; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl2; remember (XmcMod.set abs idx v) as xmpax2;
  assert(Hget_xmpax2: get xmpax2 idx = Some v) by ( subst xmpax2; rewrite XmcMod.map_get_set; auto)
  end.
  (* CSL_XMC_setXMPAXL (os_code_defs.index ′, mpaxl ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax2: (length xmpaxvl2 = 32)%nat).
  { subst xmpaxvl2.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqxmpaxvl1 in Heqxmpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_mpax': Hget_xmpax2.
  lets Heq_xh2: update_nth Heq_xh1'; try erewrite <- Heqxmpaxvl2 in Heq_xh2.
  lets Heq_xl2: nth_upd_neqrev Heq_xl1'; try erewrite <- Heqxmpaxvl2 in Heq_xl2.
  auto with zarith.
  lets Heq_xl2': nth_val_nth_val'_some_eq Heq_xl2.
  lets Heq_xh2': nth_val_nth_val'_some_eq Heq_xh2.
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  rewrite Heq_xl2'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXL_rule; [ | eauto | | | | try rewrite Hget_xmpax2; eauto | | | ] ; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq9 in *. rewrite Hset_eq9_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXL _,
  H1: ?v1 = set_mpax_struct abs_mpaxl1 _ _,
  H2: ?v2 = XmcMod.set xmpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxl2' & ?);
  subst v1; subst v2
  end.
  rewrite Heqxmpaxvl1 in Heqxmpaxvl2.
  rewrite <- Heqxmpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2)) xmpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  (* unfolds; introv Hf; tryfalse. *)
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq10: vll = vll')
  end.
  { rewrite Hset_eq9 in *. rewrite Hset_eq9_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxl = Some (lsms_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsl1: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxl
                                         = Some (lsms_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 3%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxl); eauto.
  rewrite <- Hset_eq10; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh9'.
  apply ex_intro_rule; intro evh10'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq10_conv end.
  (* sms_mpaxl ′ → smsmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_raddr =ₑ (ksDomains ′ [ksCurDomain ′]) .. dom_t_pAddress ≫ ′ 12;ₛ *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl2; remember (SmsMod.set abs idx v) as sms_mpax2;
  assert(Hget_sms2: get sms_mpax2 idx = Some v) by ( subst sms_mpax2; rewrite SmsMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSMSMPAXL (coreNum ′, os_code_defs.index ′, sms_mpaxl ′);ₛ *)
  (* unfold SMSMPAX *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert (Hlen_sms2: (length sms_mpaxvl2 = 16)%nat).
  { subst sms_mpaxvl2.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqsms_mpaxvl1 in Heqsms_mpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_smsh2: update_nth Heq_smsh1'; try erewrite <- Heqsms_mpaxvl2 in Heq_smsh2.
  lets Heq_smsl2: nth_upd_neqrev Heq_smsl1'; try erewrite <- Heqsms_mpaxvl2 in Heq_smsl2.
  auto with zarith.
  lets Heq_smsl2': nth_val_nth_val'_some_eq Heq_smsl2.
  lets Heq_smsh2': nth_val_nth_val'_some_eq Heq_smsh2.
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  rewrite Heq_smsl2'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXL_rule;  [ | | eauto | | | | try rewrite Hget_sms2; eauto | | | ] ;
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq10 in *. rewrite Hset_eq10_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXL _,
  H1: ?v1 = set_mpax_struct abs_smsl1 _ _,
  H2: ?v2 =  SmsMod.set sms_mpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_smsl1' & ?);
  subst v1; subst v2
  end.
  rewrite Heqsms_mpaxvl1 in Heqsms_mpaxvl2.
  rewrite <- Heqsms_mpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2)) sms_mpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  (* unfolds; introv Hf; tryfalse. *)
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq11: vll = vll')
  end.
  { rewrite Hset_eq10 in *. rewrite Hset_eq10_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxl = Some (lses_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesl1: Get_struct (Set_struct vll q tp vl' )  lses_mpaxl
                                         = Some (lses_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxl); eauto.
  rewrite <- Hset_eq11; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh11'.
  apply ex_intro_rule; intro evh12'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq11_conv end.
  (* ses_mpaxl ′ → sesmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_raddr =ₑ (ksDomains ′ [ksCurDomain ′]) .. dom_t_pAddress ≫ ′ 12;ₛ  *)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_struct_aop_typeneq;
                            [ intro s_; split; intro Hsat; try sep pauto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                            | simpl;auto
                            | simpl; auto
                            | unfold id_nth; simpl; auto
                            | simpl; auto
                            | intros; intro; tryfalse
                            | intros; intro; tryfalse
                            | auto
                            | idtac
                            | apply assign_type_match_true; simpl; auto
                            | simpl
                            | simpl; auto
                            | li_sepauto li ].
  introv Hsat.
  eapply bop_rv.
  sep_get_rv_array_struct_gen.
  sep get rv.
  simpl bop_eval.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  auto with zarith.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl2; remember (SesMod.set abs idx v) as ses_mpax2;
  assert(Hget_ses2: get ses_mpax2 idx = Some v) by ( subst ses_mpax2; rewrite SesMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSESMPAXL (coreNum ′, os_code_defs.index ′, ses_mpaxl ′);ₛ *)
  (* unfold SESMPAX *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert (Hlen_ses2: (length ses_mpaxvl2 = 16)%nat).
  { subst ses_mpaxvl2.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqses_mpaxvl1 in Heqses_mpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHIPARTIONCUR * 2))); eauto.
  unfold MPAXSHIPARTIONCUR. auto with zarith.
  lets Heq_sesh2: update_nth Heq_sesh1'; try erewrite <- Heqses_mpaxvl2 in Heq_sesh2.
  lets Heq_sesl2: nth_upd_neqrev Heq_sesl1'; try erewrite <- Heqses_mpaxvl2 in Heq_sesl2.
  auto with zarith.
  lets Heq_sesl2': nth_val_nth_val'_some_eq Heq_sesl2.
  lets Heq_sesh2': nth_val_nth_val'_some_eq Heq_sesh2.
  unfold MPAXSHIPARTIONCUR in *.
  change (Int.unsigned ($ 6)) with 6 in *.
  rewrite Heq_sesl2'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply forward_rule1.
  2:{
  (* eapply seq_rule. *)
  eapply csl_msmc_setSESMPAXL_rule; [ | | eauto | | | | try rewrite Hget_ses2; eauto | | | ] ;
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq11 in *. rewrite Hset_eq11_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  }
  {
  simpl spec_code_cons'. simpl init_mpax_after_if.
  introv Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  rewrite Heqxmpaxvl1 in *.
  rewrite Heqsms_mpaxvl1 in *.
  rewrite Heqses_mpaxvl1 in *.
  sep normal.
  sep eexists.
  sep cancel Aier.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel A_isr_is_prop.
  sep cancel A_dom_lenv.
  sep cancel Aop.
  sep cancel p_local.
  sep cancel segSize.
  sep cancel coreNum.
  sep cancel paddress.
  sep cancel vaddress.
  sep cancel os_code_defs.index.
  sep cancel mpaxh.
  sep cancel mpaxl.
  sep cancel ses_mpaxh.
  sep cancel ses_mpaxl.
  sep cancel sms_mpaxh.
  sep cancel sms_mpaxl.
  sep cancel ksCurDomain.
  sep cancel ksDomains.
  sep cancel Asms_mpaxinfo.
  sep cancel Axmpaxinfo.
  sep_lifts_trms AKsDomains'.
  eapply AKsDomains'_select_sn_strong_frm with (idx:= Z.to_nat (Int.unsigned vcurd)); eauto.
  unfold nat_of_Z. solve_part_int_rgn.
  unfold node_offt.
  sep normal; sep eexists.
  sep cancel AKsDomains'.
  sep cancel AKsDomains'.
  sep cancel USER_INT_MAX_N.
  sep_lifts_trms_in Hsat (evstructheap).
  sep_lifts_trms evstructheap.
  match goal with
  H: _ |= HEvStructHeap ?vll ** _ |- _ |= HEvStructHeap ?vll' ** _ =>
  assert (Hset_eq12: vll = vll')
  end.
  { rewrite Hset_eq11 in *. rewrite Hset_eq11_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  sep split.
  sep cancel os_ucos_h.domain_t.
  sep_lifts_trms ARootTaskStk'.
  eapply ARootTaskStk'_select_sn_strong_frm.
  eexists (Z.to_nat (Int.unsigned domid)).
  sep eexists.
  rewrite Htsk_addr.
  sep cancel RootTaskStk.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Aarray.
  sep split; eauto.
  sep split in Hsat.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXL _,
  H1: ?v1 = set_mpax_struct abs_sesl1 _ _,
  H2: ?v2 =  SesMod.set ses_mpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_sesl1' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqses_mpaxvl2 in *.
  sep_lifts_trms Ases_mpaxinfo.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHIPARTIONCUR * 2)) ses_mpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHIPARTIONCUR * 2)).
  sep eexists.
  unfold MPAXSHIPARTIONCUR.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  sep_lifts_trms AEvStructHeap.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  rewrite <- Hset_eq12.
  sep cancel evstructheap.
  sep cancel kscurdom.
  sep cancel ksdoms.
  sep cancel rootsk.
  sep cancel osxmpax.
  sep cancel ossms_mpax.
  sep cancel osses_mpax.
  auto.
  Optimize Proof.
  Optimize Heap.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  eauto.
  eauto.
  eauto.
  rewrite get_struct_vl'; auto.
  splits; eauto.
  rewrite <- Hset_eq12.
  do 3 try (rewrite get_set_struct_notequal; eauto).
  eapply Hno_dup with (i:= 1%nat) (j:= 2%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 2%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 2%nat); eauto.
  rewrite <- Hset_eq12.
  rewrite get_set_struct_notequal; eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 5%nat); eauto.
  rewrite <- Hset_eq12.
  do 4 try (rewrite get_set_struct_notequal; eauto).
  eapply Hno_dup with (i:= 2%nat) (j:= 4%nat); eauto.
  eapply Hno_dup with (i:= 1%nat) (j:= 4%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 4%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 4%nat); eauto.
  rewrite <- Hset_eq12.
  do 2 try (rewrite get_set_struct_notequal; eauto).
  eapply Hno_dup with (i:= 5%nat) (j:= 1%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 1%nat); eauto.
  rewrite <- Hset_eq12.
  do 5 try (rewrite get_set_struct_notequal; eauto).
  eapply Hno_dup with (i:= 4%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 2%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); eauto.
  eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); eauto.
(* R_SES_Mpax_P *)
  eapply R_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  rewrite Heqses_mpaxvl2.
  rewrite Heqses_mpax2.
  eapply R_SES_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite nth_upd_neqrev; eauto.
  erewrite update_nth; eauto.
  eapply R_SES_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_SES_Mpax_P *)
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  rewrite Heqses_mpax2.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
(* R_SMS_Mpax_P *)
  rewrite <- Heqsms_mpaxvl2.
  rewrite <- Heqsms_mpax2.
  eapply R_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  rewrite Heqsms_mpaxvl2.
  rewrite Heqsms_mpax2.
  eapply R_SMS_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite nth_upd_neqrev; eauto.
  erewrite update_nth; eauto.
  eapply R_SMS_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_SMS_Mpax_P *)
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
(* R_XMpax_P *)
  rewrite <- Heqxmpaxvl2.
  rewrite <- Heqxmpax2.
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  rewrite Heqxmpaxvl2.
  rewrite Heqxmpax2.
  eapply R_XMC_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite nth_upd_neqrev; eauto.
  erewrite update_nth; eauto.
  eapply R_XMC_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_XMC_Mpax_P *)
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  splits.
  unfolds typelen; eauto.
  unfolds; eauto.
(* array_type_vallist_match char_t int_vl *)
  splits; unfolds; eauto.
  auto.
}
  subst H11.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, kscurdom).
  eapply abscsq_rule.
  apply noabs_oslinv.
  assert (Hvrange: vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
(* vcurd = Int.mone *)
  destruct Hvrange as [Hvrange | Hvrange](* ; subst *).
  simpl spec_code_cons'. simpl init_mpax_if.
  assert (Ht: Int.eq vcurd Int.mone = true).
  { rewrite Hvrange; auto. }
  rewrite Ht.
  eapply initmpax_absimp_cdom_err; eauto.
  can_change_aop_solver.
(* vcurd <> Int.mone *)
  eapply Int.eq_false in Hvrange.
  rewrite Hvrange.
  simpl spec_code_cons'. simpl init_mpax_after_if.
  apply absinfer_eq.
  apply absinfer_eq.
(* index ′ =ₑ ′ MPAXSHAREDAREA;ₛ *)
  hoare forward.
(* vaddress ′ =ₑ ′ 201326592;ₛ *)
  hoare forward.
(* paddress ′ =ₑ vaddress ′;ₛ *)
  hoare forward.
(* segSize ′ =ₑ ′ 19;ₛ *)
  hoare forward.
  rename v'3 into xmpaxvl0.
  rename v'4 into xmpax0.
  rename v'5 into sms_mpaxvl0.
  rename v'6 into sms_mpax0.
  rename v'7 into ses_mpaxvl0.
  rename v'8 into ses_mpax0.
  rename v'9 into evstructs0.
(* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxh); eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh1.
  apply ex_intro_rule; intro evh2.
  hoare_split_pure_all.
(* mpaxh ′ → mpaxh_segSize =ₑ segSize ′;ₛ  *)
  hoare forward.
(* mpaxh ′ → mpaxh_bAddr =ₑ vaddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  unfold AXMpax.
  hoare_lifts_trms_pre (RH_XMpax_P, R_XMpax_P).
  apply pure_split_rule'; introv Hrh_xmpax.
  apply pure_split_rule'; introv Hr_xmpax.
  assert (Hget_xmpax:  exists mpaxl mpaxh, get xmpax0 ($ MPAXSHAREDAREA) = Some (mpaxl, mpaxh)).
  { eapply Hrh_xmpax; unfold MPAXSHAREDAREA.
     change ( Int.unsigned ($ 4)) with 4; auto with zarith.
  }
  destruct Hget_xmpax as (abs_mpaxl & abs_mpaxh & Hget_xmpax).
  (* CSL_XMC_setXMPAXH (os_code_defs.index ′, mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  hoare_assert_pure (length xmpaxvl0 = 32)%nat.
  { unfold Axmpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_xmpax.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2 + 1))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_mpax: Hget_xmpax.
  eapply Hr_xmpax in Heq_mpax.
  destruct Heq_mpax as (Heq_xl & Heq_xh).
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  lets Heq_xl': Heq_xl; lets Heq_xh': Heq_xh.
  eapply nth_val_nth_val'_some_eq in Heq_xl, Heq_xh.
  rewrite Heq_xh.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXH_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
     update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2 + 1)) xmpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2 + 1)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq1: vll = vll')
  end.
  { eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxh = Some (lsms_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsh: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxh
                                         = Some (lsms_mpaxh, tp', vl''))
  end.
  {  rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 4%nat); simpl; eauto. }

(* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxh); eauto.
  rewrite <- Hset_eq1; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh3.
  apply ex_intro_rule; intro evh4.
  hoare_split_pure_all.
  match goal with H:_ ++ (_ :: _) = _ ++ (_ :: _) |- _ =>
  rename H into Hset_eq1_conv end.
(* sms_mpaxh ′ → smsmpaxh_segSz =ₑ segSize ′;ₛ  *)
  hoare forward.
(* sms_mpaxh ′ → smsmpaxh_bAddr =ₑ vaddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASMSMpax *)
  unfold ASMSMpax.
  hoare_lifts_trms_pre (RH_SMS_Mpax_P, R_SMS_Mpax_P).
  apply pure_split_rule'; introv Hrh_sms.
  apply pure_split_rule'; introv Hr_sms.
  assert (Hget_sms:  exists mpaxl mpaxh, get sms_mpax0 ($ MPAXSHAREDAREA) = Some (mpaxl, mpaxh)).
  { eapply Hrh_sms; unfold MPAXSHAREDAREA.
     change ( Int.unsigned ($ 4)) with 4; auto with zarith.
  }
  destruct Hget_sms as (abs_smsl & abs_smsh & Hget_sms).
  (* CSL_MSMC_setSMSMPAXH (coreNum ′, index ′, sms_mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  hoare_assert_pure (length sms_mpaxvl0 = 16)%nat.
  { unfold Asms_mpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_sms.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2 + 1))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_mpax: Hget_sms.
  eapply Hr_sms in Heq_mpax.
  destruct Heq_mpax as (Heq_smsl & Heq_smsh).
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  lets Heq_smsl': Heq_smsl; lets Heq_smsh': Heq_smsh.
  eapply nth_val_nth_val'_some_eq in Heq_smsl, Heq_smsh.
  rewrite Heq_smsh.
  hoare_split_pure_all.
  assert (Heq_dnum: Z.of_nat (Z.to_nat DNUM) = DNUM).
  { pose proof dnum_range.
    auto with zarith. }
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
        do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq1 in *. rewrite Hset_eq1_conv in *.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold SMSMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
     update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2 + 1)) sms_mpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2 + 1)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq2: vll = vll')
  end.
  { rewrite Hset_eq1 in *. rewrite Hset_eq1_conv in *.
    eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxh = Some (lses_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesh: Get_struct (Set_struct vll q tp vl' )  lses_mpaxh
                                         = Some (lses_mpaxh, tp', vl''))
  end.
  {  try repeat rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 2%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
    eapply backward_rule1.
    introv Hsat.
    sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxh).
    eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxh); eauto.
    rewrite <- Hset_eq2; eauto.
    hoare normal pre.
    apply ex_intro_rule; intro evh5.
    apply ex_intro_rule; intro evh6.
    hoare_split_pure_all.
    match goal with H:_ ++ (_ :: _) = _ ++ (_ :: _) |- _ =>
    rename H into Hset_eq2_conv end.
(* ses_mpaxh ′ → sesmpaxh_segSz =ₑ segSize ′;ₛ  *)
  hoare forward.
(* ses_mpaxh ′ → sesmpaxh_bAddr =ₑ vaddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASESMpax *)
  unfold ASESMpax.
  hoare_lifts_trms_pre (RH_SES_Mpax_P, R_SES_Mpax_P).
  apply pure_split_rule'; introv Hrh_ses.
  apply pure_split_rule'; introv Hr_ses.
  assert (Hget_ses:  exists mpaxl mpaxh, get ses_mpax0 ($ MPAXSHAREDAREA) = Some (mpaxl, mpaxh)).
  { eapply Hrh_ses; unfold MPAXSHAREDAREA.
     change ( Int.unsigned ($ 4)) with 4; auto with zarith.
  }
  destruct Hget_ses as (abs_sesl & abs_sesh & Hget_ses).
  (* CSL_MSMC_setSESMPAXH (coreNum ′, index ′, ses_mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  hoare_assert_pure (length ses_mpaxvl0 = 16)%nat.
  { unfold Ases_mpaxinfo in *.
     eapply Aarray_vl_len_eq with (s:= s0).
     sep pauto.
  }
  apply pure_split_rule'; introv Hlen_ses.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2 + 1))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_mpax: Hget_ses.
  eapply Hr_ses in Heq_mpax.
  destruct Heq_mpax as (Heq_sesl & Heq_sesh).
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  lets Heq_sesl': Heq_sesl; lets Heq_sesh': Heq_sesh.
  eapply nth_val_nth_val'_some_eq in Heq_sesl, Heq_sesh.
  rewrite Heq_sesh.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
        do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq2 in *. rewrite Hset_eq2_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold SESMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
     update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2 + 1)) ses_mpaxvl0 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2 + 1)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq3: vll = vll')
  end.
  { rewrite Hset_eq2 in *. rewrite Hset_eq2_conv in *.
    eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lmpaxl = Some (lmpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxl: Get_struct (Set_struct vll q tp vl' )  lmpaxl
                                         = Some (lmpaxl, tp', vl''))
  end.
  {  try repeat rewrite get_set_struct_notequal; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 1%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxl); eauto.
  rewrite <- Hset_eq3; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh7.
  apply ex_intro_rule; intro evh8.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq3_conv end.
  (* mpaxl′→mpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* mpaxl′→mpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl ′ → mpaxl_rAddr =ₑ pAddress ′ ≫ ′ 12;ₛ  *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl1; remember (XmcMod.set abs idx v) as xmpax1;
  assert(Hget_xmpax1: get xmpax1 idx = Some v) by ( subst xmpax1; rewrite XmcMod.map_get_set; auto)
  end.
  (* CSL_XMC_setXMPAXL (os_code_defs.index ′, mpaxl ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax1: (length xmpaxvl1 = 32)%nat).
  { subst xmpaxvl1.
     rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_mpax: Hget_xmpax1.
  lets Heq_xl1: nth_upd_neqrev Heq_xl'; try erewrite <- Heqxmpaxvl1 in Heq_xl1.
  auto with zarith.
  lets Heq_xl1': nth_val_nth_val'_some_eq Heq_xl1.
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  rewrite Heq_xl1'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXL_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq3 in *. rewrite Hset_eq3_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXL _,
  H1: ?v1 = set_mpax_struct abs_mpaxl _ _,
  H2: ?v2 = XmcMod.set xmpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqxmpaxvl1.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2)) xmpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq4: vll = vll')
  end.
  { rewrite Hset_eq3 in *. rewrite Hset_eq3_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxl = Some (lsms_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsl: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxl
                                         = Some (lsms_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxl); eauto.
  rewrite <- Hset_eq4; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh9.
  apply ex_intro_rule; intro evh10.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq4_conv end.
  (* sms_mpaxl ′ → smsmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_raddr =ₑ paddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl1; remember (SmsMod.set abs idx v) as sms_mpax1;
  assert(Hget_sms1: get sms_mpax1 idx = Some v) by ( subst sms_mpax1; rewrite SmsMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSMSMPAXL (coreNum ′, os_code_defs.index ′, sms_mpaxl ′);ₛ *)
  (* unfold SMSMPAX *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert (Hlen_sms1: (length sms_mpaxvl1 = 16)%nat).
  { subst sms_mpaxvl1.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_sms: Hget_sms1.
  lets Heq_smsl1: nth_upd_neqrev Heq_smsl'; try erewrite <- Heqsms_mpaxvl1 in Heq_smsl1.
  auto with zarith.
  lets Heq_smsl1': nth_val_nth_val'_some_eq Heq_smsl1.
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  rewrite Heq_smsl1'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXL_rule;  [ | | eauto | | | | try rewrite Hget_sms1; eauto | | | ] ;
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq4 in *. rewrite Hset_eq4_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXL _,
  H1: ?v1 = set_mpax_struct abs_smsl _ _,
  H2: ?v2 =  SmsMod.set sms_mpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_smsl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqsms_mpaxvl1.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2)) sms_mpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq5: vll = vll')
  end.
  { rewrite Hset_eq4 in *. rewrite Hset_eq4_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxl = Some (lses_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesl: Get_struct (Set_struct vll q tp vl' )  lses_mpaxl
                                         = Some (lses_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxl); eauto.
  rewrite <- Hset_eq5; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh11.
  apply ex_intro_rule; intro evh12.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq5_conv end.
  (* ses_mpaxl ′ → sesmpaxl_ux =ₑ ′1;ₛ *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_uw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_ur =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_raddr =ₑ paddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl1; remember (SesMod.set abs idx v) as ses_mpax1;
  assert(Hget_ses1: get ses_mpax1 idx = Some v) by ( subst ses_mpax1; rewrite SesMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSESMPAXL (coreNum ′, os_code_defs.index ′, ses_mpaxl ′);ₛ *)
  (* unfold SESMPAX *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert (Hlen_ses1: (length ses_mpaxvl1 = 16)%nat).
  { subst ses_mpaxvl1.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXSHAREDAREA * 2))); eauto.
  unfold MPAXSHAREDAREA. auto with zarith.
  lets Heq_ses: Hget_ses1.
  lets Heq_sesl1: nth_upd_neqrev Heq_sesl'; try erewrite <- Heqses_mpaxvl1 in Heq_sesl1.
  auto with zarith.
  lets Heq_sesl1': nth_val_nth_val'_some_eq Heq_sesl1.
  unfold MPAXSHAREDAREA in *.
  change (Int.unsigned ($ 4)) with 4 in *.
  rewrite Heq_sesl1'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXL_rule;  [ | | eauto | | | | try rewrite Hget_ses1; eauto | | | ] ;
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq5 in *. rewrite Hset_eq5_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXL _,
  H1: ?v1 = set_mpax_struct abs_sesl _ _,
  H2: ?v2 =  SesMod.set ses_mpax1 _ _ |- _ =>
  destruct H0 as (Hget_set_sesl' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqses_mpaxvl1.

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXSHAREDAREA * 2)) ses_mpaxvl1 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXSHAREDAREA * 2)).
  sep eexists.
  unfold MPAXSHAREDAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses1; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  unfolds; introv Hf; tryfalse.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq6: vll = vll')
  end.
  { rewrite Hset_eq5 in *. rewrite Hset_eq5_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lmpaxh = Some (lmpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxh1: Get_struct (Set_struct vll q tp vl' )  lmpaxh
                                         = Some (lmpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 4%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 0%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 0%nat); simpl; eauto. }
  clear Hset_eq1 (* Hget_set_smsh *) Hset_eq1_conv 
        Hset_eq2 (* Hget_set_sesh *)  Hset_eq2_conv
        Hset_eq3 (* Hget_set_mpaxl *) Hset_eq3_conv (* Hget_set_mpaxl' *)
        Hset_eq4 (* Hget_set_smsl *) Hset_eq4_conv (* Hget_set_smsl' *)
        Hset_eq5 (* Hget_set_sesl *) Hset_eq5_conv (* Hget_set_sesl' *).
(* index ′ =ₑ ′ MPAXALLAREA;ₛ *)
  hoare forward.
(* vaddress ′ =ₑ ′ 201326592;ₛ *)
  hoare forward.
(* paddress ′ =ₑ vaddress ′;ₛ *)
  hoare forward.
(* segSize ′ =ₑ ′ 21;ₛ *)
  hoare forward.
(* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxh); eauto.
  rewrite <- Hset_eq6; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh1'.
  apply ex_intro_rule; intro evh2'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq6_conv end.
(* mpaxh ′ → mpaxh_segSize =ₑ segSize ′;ₛ  *)
  hoare forward.
(* mpaxh ′ → mpaxh_bAddr =ₑ vaddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl2; remember (XmcMod.set abs idx v) as xmpax2
  end.
  assert(Hget_xmpax2: exists mpaxl mpaxh,  get xmpax2 ($ MPAXALLAREA) = Some (mpaxl, mpaxh)).
  { subst xmpax2.
     do 2 try rewrite XmcMod.map_get_set'; auto.
     eapply Hrh_xmpax; unfold MPAXALLAREA.
     change ( Int.unsigned ($ 3)) with 3; auto with zarith.
  }
  destruct Hget_xmpax2 as (abs_mpaxl2 & abs_mpaxh2 & Hget_xmpax2).
  (* CSL_XMC_setXMPAXH (os_code_defs.index ′, mpaxh ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax2: (length xmpaxvl2 = 32)%nat).
  { subst xmpaxvl2.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2 + 1))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_mpax2: Hget_xmpax2.
  rewrite  Heqxmpax2 in Heq_mpax2.
  do 2 try rewrite XmcMod.map_get_set' in Heq_mpax2; auto.
  eapply Hr_xmpax in Heq_mpax2.
  destruct Heq_mpax2 as (Heq_xl2 & Heq_xh2).
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  do 2 try eapply nth_upd_neqrev in Heq_xl2;
  try erewrite <- Heqxmpaxvl2 in Heq_xl2; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_xh2;
  try erewrite <- Heqxmpaxvl2 in Heq_xh2; try solve [auto with zarith].
  lets Heq_xl2': Heq_xl2; lets Heq_xh2': Heq_xh2.
  eapply nth_val_nth_val'_some_eq in Heq_xl2, Heq_xh2.
  rewrite Heq_xh2.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXH_rule; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq6 in *. rewrite Hset_eq6_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXH _,
  H1: ?v1 = set_mpax_struct abs_mpaxh2 _ _,
  H2: ?v2 = XmcMod.set xmpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqxmpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2 + 1)) xmpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2 + 1)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  unfold MPAXALLAREA in *.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  unfold MPAXALLAREA in *; auto with zarith.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq7: vll = vll')
  end.
  { rewrite Hset_eq6 in *. rewrite Hset_eq6_conv in *.
    eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxh = Some (lsms_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsh1: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxh
                                         = Some (lsms_mpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 2%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 4%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 4%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
    eapply backward_rule1.
    introv Hsat.
    sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxh).
    eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxh); eauto.
    rewrite <- Hset_eq7; eauto.
    hoare normal pre.
    apply ex_intro_rule; intro evh3'.
    apply ex_intro_rule; intro evh4'.
    hoare_split_pure_all.
    match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq7_conv end.
  (* sms_mpaxh ′ → smsmpaxh_segSz =ₑ segSize ′;ₛ  *)
    hoare forward.
  (* sms_mpaxh ′ → smsmpaxh_bAddr ′ ≫ ′ 12;ₛ *)
    hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASMSMpax*)
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl2; remember (SmsMod.set abs idx v) as sms_mpax2
  end.
  assert(Hget_sms2: exists mpaxl mpaxh,  get sms_mpax2 ($ MPAXALLAREA) = Some (mpaxl, mpaxh)).
  { subst sms_mpax2.
     do 2 try rewrite SmsMod.map_get_set'; auto.
     eapply Hrh_sms; unfold MPAXALLAREA.
     change ( Int.unsigned ($ 3)) with 3; auto with zarith.
  }
  destruct Hget_sms2 as (abs_smsl2 & abs_smsh2 & Hget_sms2).
  (* CSL_MSMC_setSMSMPAXH (coreNum ′,os_code_defs.index ′,sms_mpaxh ′);ₛ *)
  (* unfold ASMSMpax *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert(Hlen_sms2: (length sms_mpaxvl2 = 16)%nat).
  { subst sms_mpaxvl2.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2 + 1))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_mpax2: Hget_sms2.
  rewrite  Heqsms_mpax2 in Heq_mpax2.
  do 2 try rewrite SmsMod.map_get_set' in Heq_mpax2; auto.
  eapply Hr_sms in Heq_mpax2.
  destruct Heq_mpax2 as (Heq_smsl2 & Heq_smsh2).
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  do 2 try eapply nth_upd_neqrev in Heq_smsl2;
  try erewrite <- Heqsms_mpaxvl2 in Heq_smsl2; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_smsh2;
  try erewrite <- Heqsms_mpaxvl2 in Heq_smsh2; try solve [auto with zarith].
  lets Heq_smsl2': Heq_smsl2; lets Heq_smsh2': Heq_smsh2.
  eapply nth_val_nth_val'_some_eq in Heq_smsl2, Heq_smsh2.
  rewrite Heq_smsh2.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq7 in *. rewrite Hset_eq7_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXH _,
  H1: ?v1 = set_mpax_struct abs_smsh2 _ _,
  H2: ?v2 =  SmsMod.set sms_mpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_smsh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqsms_mpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2 + 1)) sms_mpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2 + 1)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  unfold MPAXALLAREA in *.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq8: vll = vll')
  end.
  { rewrite Hset_eq7 in *. rewrite Hset_eq7_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxh = Some (lses_mpaxh, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesh1: Get_struct (Set_struct vll q tp vl' )  lses_mpaxh
                                         = Some (lses_mpaxh, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 1%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 5%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 2%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 2%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxh).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxh); eauto.
  rewrite <- Hset_eq8; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh5'.
  apply ex_intro_rule; intro evh6'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq8_conv end.
  (* ses_mpaxh ′ → sesmpaxh_segSz =ₑ segSize ′;ₛ  *)
    hoare forward.
  (* ses_mpaxh ′ → sesmpaxh_bAddr ′ ≫ ′ 12;ₛ *)
    hoare forward.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj; eauto.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxh; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* unfold ASESMpax*)
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl2; remember (SesMod.set abs idx v) as ses_mpax2
  end.
  assert(Hget_ses2: exists mpaxl mpaxh,  get ses_mpax2 ($ MPAXALLAREA) = Some (mpaxl, mpaxh)).
  { subst ses_mpax2.
     do 2 try rewrite SesMod.map_get_set'; auto.
     eapply Hrh_ses; unfold MPAXALLAREA.
     change ( Int.unsigned ($ 3)) with 3; auto with zarith.
  }
  destruct Hget_ses2 as (abs_sesl2 & abs_sesh2 & Hget_ses2).
  (* CSL_MSMC_setSESMPAXH (coreNum ′,os_code_defs.index ′,ses_mpaxh ′);ₛ *)
  (* unfold ASESMpax *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert(Hlen_ses2: (length ses_mpaxvl2 = 16)%nat).
  { subst ses_mpaxvl2.
     do 2 try rewrite update_nth_val_len_eq; auto.
  }
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2 + 1))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_mpax2: Hget_ses2.
  rewrite  Heqses_mpax2 in Heq_mpax2.
  do 2 try rewrite SesMod.map_get_set' in Heq_mpax2; auto.
  eapply Hr_ses in Heq_mpax2.
  destruct Heq_mpax2 as (Heq_sesl2 & Heq_sesh2).
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  do 2 try eapply nth_upd_neqrev in Heq_sesl2;
  try erewrite <- Heqses_mpaxvl2 in Heq_sesl2; try solve [auto with zarith].
  do 2 try eapply nth_upd_neqrev in Heq_sesh2;
  try erewrite <- Heqses_mpaxvl2 in Heq_sesh2; try solve [auto with zarith].
  lets Heq_sesl2': Heq_sesl2; lets Heq_sesh2': Heq_sesh2.
  eapply nth_val_nth_val'_some_eq in Heq_sesl2, Heq_sesh2.
  rewrite Heq_sesh2.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXH_rule; eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq8 in *. rewrite Hset_eq8_conv in *.
         erewrite Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMpax *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXH _,
  H1: ?v1 = set_mpax_struct abs_sesh2 _ _,
  H2: ?v2 =  SesMod.set ses_mpax2 _ _ |- _ =>
  destruct H0 as (Hget_set_sesh' & ?);
  subst v1; subst v2
  end.
  rewrite <- Heqses_mpaxvl2.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2 + 1)) ses_mpaxvl2 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2 + 1)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  unfold MPAXALLAREA in *.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses2; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxh).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq9: vll = vll')
  end.
  { rewrite Hset_eq8 in *. rewrite Hset_eq8_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpax *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lmpaxl = Some (lmpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_mpaxl1: Get_struct (Set_struct vll q tp vl' )  lmpaxl
                                         = Some (lmpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 5%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 3%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 1%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 1%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= mpaxl); eauto.
  rewrite <- Hset_eq9; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh7'.
  apply ex_intro_rule; intro evh8'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq9_conv end.
  (* mpaxl′→mpaxl_ux =ₑ ′0;ₛ *)
  hoare forward.
  (* mpaxl′→mpaxl_uw =ₑ ′0;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_ur =ₑ ′0;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl′→mpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* mpaxl ′ → mpaxl_rAddr =ₑ paddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Axmpaxinfo, osxmpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Axmpaxinfo ?vl ** Hxmpax (XmcMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as xmpaxvl3; remember (XmcMod.set abs idx v) as xmpax3;
  assert(Hget_xmpax3: get xmpax3 idx = Some v) by ( subst xmpax3; rewrite XmcMod.map_get_set; auto)
  end.
  (* CSL_XMC_setXMPAXL (os_code_defs.index ′, mpaxl ′);ₛ *)
  (* unfold XMPAX *)
  hoare_lifts_trms_pre Axmpaxinfo.
  assert (Hlen_xmpax3: (length xmpaxvl3 = 32)%nat).
  { subst xmpaxvl3.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqxmpaxvl2 in Heqxmpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Axmpaxinfo).
  eapply Axmpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_mpax': Hget_xmpax3.
  lets Heq_xh3: update_nth Heq_xh2'; try erewrite <- Heqxmpaxvl3 in Heq_xh3.
  lets Heq_xl3: nth_upd_neqrev Heq_xl2'; try erewrite <- Heqxmpaxvl3 in Heq_xl3.
  auto with zarith.
  lets Heq_xl3': nth_val_nth_val'_some_eq Heq_xl3.
  lets Heq_xh3': nth_val_nth_val'_some_eq Heq_xh3.
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  rewrite Heq_xl3'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_setXMPAXL_rule; [ | eauto | | | | try rewrite Hget_xmpax3; eauto | | | ] ; eauto.
  3:{ introv Hsat.
         split; sep get rv. }
  3:{ introv Hsat.
         sep pauto.
         rewrite Hset_eq9 in *. rewrite Hset_eq9_conv in *.
         split.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold XMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match XMC_XMPAXL _,
  H1: ?v1 = set_mpax_struct abs_mpaxl2 _ _,
  H2: ?v2 = XmcMod.set xmpax3 _ _ |- _ =>
  destruct H0 as (Hget_set_mpaxl3' & ?);
  subst v1; subst v2
  end.
  rewrite Heqxmpaxvl2 in Heqxmpaxvl3.
  rewrite <- Heqxmpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (xmpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Axmpaxinfo_fold_frm with (xmpaxvl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2)) xmpaxvl3 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (xmpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (xmpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel xmpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_xmpax3; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lmpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  (* unfolds; introv Hf; tryfalse. *)
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq10: vll = vll')
  end.
  { rewrite Hset_eq9 in *. rewrite Hset_eq9_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign xmpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lsms_mpaxl = Some (lsms_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_smsl1: Get_struct (Set_struct vll q tp vl' )  lsms_mpaxl
                                         = Some (lsms_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 3%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 0%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 5%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 5%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, sms_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= sms_mpaxl); eauto.
  rewrite <- Hset_eq10; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh9'.
  apply ex_intro_rule; intro evh10'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq10_conv end.
  (* sms_mpaxl ′ → smsmpaxl_ux =ₑ ′ 0;ₛ *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_uw =ₑ ′ 0;ₛ *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_ur =ₑ ′ 0;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* sms_mpaxl ′ → smsmpaxl_raddr =ₑ paddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Asms_mpaxinfo, ossms_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Asms_mpaxinfo ?vl ** Hsms_mpax (SmsMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as sms_mpaxvl3; remember (SmsMod.set abs idx v) as sms_mpax3;
  assert(Hget_sms3: get sms_mpax3 idx = Some v) by ( subst sms_mpax3; rewrite SmsMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSMSMPAXL (coreNum ′, index ′, sms_mpaxl ′);ₛ *)
  (* unfold SMSMPAX *)
  hoare_lifts_trms_pre Asms_mpaxinfo.
  assert (Hlen_sms3: (length sms_mpaxvl3 = 16)%nat).
  { subst sms_mpaxvl3.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqsms_mpaxvl2 in Heqsms_mpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Asms_mpaxinfo).
  eapply Asms_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_smsh3: update_nth Heq_smsh2'; try erewrite <- Heqsms_mpaxvl3 in Heq_smsh3.
  lets Heq_smsl3: nth_upd_neqrev Heq_smsl2'; try erewrite <- Heqsms_mpaxvl3 in Heq_smsl3.
  auto with zarith.
  lets Heq_smsl3': nth_val_nth_val'_some_eq Heq_smsl3.
  lets Heq_smsh3': nth_val_nth_val'_some_eq Heq_smsh3.
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  rewrite Heq_smsl3'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSMSMPAXL_rule; [ | | eauto | | | | try rewrite Hget_sms3; eauto | | | ] ; 
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq10 in *. rewrite Hset_eq10_conv in *.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASMSMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SMSMPAXL _,
  H1: ?v1 = set_mpax_struct abs_smsl2 _ _,
  H2: ?v2 = SmsMod.set sms_mpax3 _ _ |- _ =>
  destruct H0 as (Hget_set_smsl3' & ?);
  subst v1; subst v2
  end.
  rewrite Heqsms_mpaxvl2 in Heqsms_mpaxvl3.
  rewrite <- Heqsms_mpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (sms_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Asms_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2)) sms_mpaxvl3 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (sms_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (sms_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel sms_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_sms3; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lsms_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  (* unfolds; introv Hf; tryfalse. *)
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq11: vll = vll')
  end.
  { rewrite Hset_eq10 in *. rewrite Hset_eq10_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign sms_mpaxl *)
  match goal with
  H: Set_struct ?vll ?q ?tp ?vl' = _ ,
  H': Get_struct _ lses_mpaxl = Some (lses_mpaxl, ?tp', ?vl'') |- _ =>
  assert (Hget_set_sesl1: Get_struct (Set_struct vll q tp vl' )  lses_mpaxl
                                         = Some (lses_mpaxl, tp', vl''))
  end.
  { repeat try (rewrite get_set_struct_notequal; eauto).
     eapply Hno_dup with (i:= 0%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 4%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 2%nat) (j:= 3%nat); simpl; eauto.
     eapply Hno_dup with (i:= 1%nat) (j:= 3%nat); simpl; eauto. 
     eapply Hno_dup with (i:= 5%nat) (j:= 3%nat); simpl; eauto. }
  (* unfold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (AEvStructHeap, ses_mpaxl).
  eapply AEvStructHeap_unfold_gen with (ident:= ses_mpaxl); eauto.
  rewrite <- Hset_eq11; eauto.
  hoare normal pre.
  apply ex_intro_rule; intro evh11'.
  apply ex_intro_rule; intro evh12'.
  hoare_split_pure_all.
  match goal with H: _ ++ (_ :: _) = _ ++ (_ :: _) |- _ => rename H into Hset_eq11_conv end.
  (* ses_mpaxl ′ → sesmpaxl_ux =ₑ ′ 0;ₛ *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_uw =ₑ ′ 0;ₛ *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_ur =ₑ ′ 0;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sx =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sw =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_sr =ₑ ′1;ₛ  *)
  hoare forward.
  (* ses_mpaxl ′ → sesmpaxl_raddr =ₑ paddress ′ ≫ ′ 12;ₛ *)
  hoare forward.
  change ($ 1) with Int.one in *.
  (* change absdata *)
  hoare_lifts_trms_pre (Aop, evstructheap).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply initmpax_absimp_set_mpaxl; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  hoare_lifts_trms_pre (Ases_mpaxinfo, osses_mpax).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  Ases_mpaxinfo ?vl ** Hses_mpax (SesMod.set ?abs ?idx ?v) ** _ }} _ {{ _ }} =>
  remember vl as ses_mpaxvl3; remember (SesMod.set abs idx v) as ses_mpax3;
  assert(Hget_ses3: get ses_mpax3 idx = Some v) by ( subst ses_mpax3; rewrite SesMod.map_get_set; auto)
  end.
  (* CSL_MSMC_setSESMPAXL (coreNum ′, index ′, ses_mpaxl ′);ₛ *)
  (* unfold SESMPAX *)
  hoare_lifts_trms_pre Ases_mpaxinfo.
  assert (Hlen_ses3: (length ses_mpaxvl3 = 16)%nat).
  { subst ses_mpaxvl3.
     do 3 try rewrite update_nth_val_len_eq; auto.
  }
  rewrite <- Heqses_mpaxvl2 in Heqses_mpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (Ases_mpaxinfo).
  eapply Ases_mpaxinfo_unfold_any_idx_frm with (idx:= (Z.to_nat (MPAXALLAREA * 2))); eauto.
  unfold MPAXALLAREA. auto with zarith.
  lets Heq_sesh3: update_nth Heq_sesh2'; try erewrite <- Heqses_mpaxvl3 in Heq_sesh3.
  lets Heq_sesl3: nth_upd_neqrev Heq_sesl2'; try erewrite <- Heqses_mpaxvl3 in Heq_sesl3.
  auto with zarith.
  lets Heq_sesl3': nth_val_nth_val'_some_eq Heq_sesl3.
  lets Heq_sesh3': nth_val_nth_val'_some_eq Heq_sesh3.
  unfold MPAXALLAREA in *.
  change (Int.unsigned ($ 3)) with 3 in *.
  rewrite Heq_sesl3'.
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_msmc_setSESMPAXL_rule; [ | | eauto | | | | try rewrite Hget_ses3; eauto | | | ] ; 
  eauto; try rewrite Heq_dnum.
  4:{ introv Hsat.
         do 2 (split; try sep get rv). }
  4:{ introv Hsat.
         sep pauto.
         split.
         rewrite Hset_eq11 in *. rewrite Hset_eq11_conv in *.
         eapply Get_struct_Set_vl; eauto.
         simpl. splits; auto.
  }
  can_change_aop_solver.
  clear; pose proof dnum_range; solve_part_int_rgn.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* fold ASESMPAX *)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  match goal with
  H0: Get_struct _ _ = Some _ /\ struct_type_vallist_match MSMC_SESMPAXL _,
  H1: ?v1 = set_mpax_struct abs_sesl2 _ _,
  H2: ?v2 = SesMod.set ses_mpax3 _ _ |- _ =>
  destruct H0 as (Hget_set_sesl3' & ?);
  subst v1; subst v2
  end.
  rewrite Heqses_mpaxvl2 in Heqses_mpaxvl3.
  rewrite <- Heqses_mpaxvl3.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (ses_mpax_block, Aarray_rm).
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> ?v ** _ |- _ =>
  eapply Ases_mpaxinfo_fold_frm with (vl :=
                                                                         update_nth_val (Z.to_nat(MPAXALLAREA * 2)) ses_mpaxvl3 v)
  end.
  rewrite update_nth_val_len_eq; auto.
  exists (Z.to_nat(MPAXALLAREA * 2)).
  sep eexists.
  unfold MPAXALLAREA.
  rewrite Int.mul_commut.
  rewrite <- Int_mul_eq; solve_part_int_rgn.
  match goal with
   H: _ |= PV (ses_mpax_block, ?i1) @ _ |-> _ ** _ |- _ |= PV (ses_mpax_block, ?i2) @ _ |-> _ ** _ =>
  assert (Heqi: i2 = i1)
  end.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  rewrite Heqi.
  sep cancel ses_mpax_block.
  eapply array_rm_update_eq_frm; eauto.
  auto with zarith.
  sep cancel Aarray_rm.
  sep split; eauto with zarith.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen_ses3; auto with zarith.
  symmetry.
  eapply nth_val_nth_val'_some_eq.
  eapply update_nth; eauto.
  rewrite Int.unsigned_repr; solve_part_int_rgn.
  (* fold AEvStructHeap *)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold' with (q:= lses_mpaxl).
  sep eexists.
  sep cancel Astruct.
  sep cancel AEvStructHeap.
  sep cancel AEvStructHeap.
  sep split; eauto.
  (* unfolds; introv Hf; tryfalse. *)
  hoare_lifts_trms_pre (AEvStructHeap, evstructheap).
  match goal with
  | |- {|_ , _, _, _, _, _|}|-_ 
  {{  AEvStructHeap ?vll' ** HEvStructHeap ?vll ** _ }} _ {{ _ }} =>
  assert (Hset_eq12: vll = vll')
  end.
  { rewrite Hset_eq11 in *. rewrite Hset_eq11_conv in *.
     eapply set_struct_update_vl_gen; eauto. }
  (* end of assign ses_mpaxl *)
  (* CSL_XMC_clearFault;ₛ *)
  unfold AXMPFR.
  unfold AMDMAER.
  hoare normal pre.
  apply ex_intro_rule; intro verr.
  apply ex_intro_rule; intro vfar.
  apply ex_intro_rule; intro vfsr.
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_xmc_clearFault_rule.
  2: { introv Hsat.
       sep pauto. }
  can_change_aop_solver.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* CSL_CGEM_clearMDMAError;ₛ *)
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  eapply csl_cgem_clearMDMAError_rule.
  2: { introv Hsat.
       sep pauto. }
  can_change_aop_solver.
  introv Hsat.
  unfold p_local in Hsat.
  unfold CurLINV.
  li_sepauto li.
  (* RETURN *)
  hoare forward.
  rewrite Hset_eq12 in *.
  change (Int.ltu ($ 12) Int.iwordsize) with true in *.
  match goal with H: _ |= _ |- _ => rename H into Hsat end.
  sep cancel AKsDomains'.
  sep cancel ARootTaskStk.
  sep cancel Axmpaxinfo.
  sep cancel Asms_mpaxinfo.
  sep cancel Ases_mpaxinfo.
  sep cancel AEvStructHeap.
  split; auto.
  clear.
  instantiate (1:= lsms_mpaxl).
  instantiate (1:= lsms_mpaxh).
  instantiate (1:= lses_mpaxl).
  instantiate (1:= lses_mpaxh).
  instantiate (1:= lmpaxl).
  instantiate (1:= lmpaxh); auto.
  unfold MPAXALLAREA.
  eapply update_nth; eauto.
  rewrite Hset_eq12 in *.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  rewrite get_mpax_struct_sesl_gen with (v:= ($ 201326592 >>ᵢ $ 12))
   (v1:= Vint32 Int.one) (v2:= Vint32 Int.one) (v3:= Vint32 Int.one)
   (v4:= V$ 0) (v5:= V$ 0) (v6:= V$ 0); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  Optimize Proof.
  Optimize Heap.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 23) by (int auto).
  change (31 - Z.of_nat (0 + 8)) with 23 in H.
  assert ( two_p 23 <two_p d <= two_p 31).
  { int auto.
    eapply two_p_monotone_strict; int auto.
    eapply two_p_monotone; int auto.
  }
  int auto.
  (* isflag (Vint32 Int.one) /\ ... *)
  unfold isflag; 
  try change ($ 0) with Int.zero;
  try change ($ 1) with Int.one.
  repeat try splits; auto.
  eapply update_nth; eauto.
  rewrite Hset_eq11 in *.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  rewrite get_mpax_struct_smsl_gen with (v:= ($ 201326592 >>ᵢ $ 12))
   (v1:= Vint32 Int.one) (v2:= Vint32 Int.one) (v3:= Vint32 Int.one)
   (v4:= V$ 0) (v5:= V$ 0) (v6:= V$ 0); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 23) by (int auto).
  change (31 - Z.of_nat (0 + 8)) with 23 in H.
  assert ( two_p 23 <two_p d <= two_p 31).
  { int auto.
    eapply two_p_monotone_strict; int auto.
    eapply two_p_monotone; int auto.
  }
  int auto.
  (* isflag (Vint32 Int.one) /\ ... *)
  unfold isflag; 
  try change ($ 0) with Int.zero;
  try change ($ 1) with Int.one.
  repeat try splits; auto.
  eapply update_nth; eauto.
  rewrite Hset_eq10 in *.
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  rewrite get_mpax_struct_xmcl_gen with (v:= ($ 201326592 >>ᵢ $ 12))
     (v1:= Vint32 Int.one) (v2:= Vint32 Int.one) (v3:= Vint32 Int.one)
     (v4:= V$ 0) (v5:= V$ 0) (v6:= V$ 0); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 23) by (int auto).
  change (31 - Z.of_nat (0 + 8)) with 23 in H.
  assert ( two_p 23 <two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone_strict; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
  (* isflag (Vint32 Int.one) /\ ... *)
  unfold isflag; 
  try change ($ 0) with Int.zero;
  try change ($ 1) with Int.one.
  repeat try splits; auto.
  erewrite nth_upd_neqrev; auto with zarith.
  eapply update_nth; eauto.
  rewrite Hset_eq9 in *.
  rewrite get_mpax_struct_sesh_gen with 
     (v:= ($ 201326592 >>ᵢ $ 12))
     (v1:= $ 21); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 19) by (int auto).
  change (31 - Z.of_nat (12 + 0)) with 19 in H.
  assert ( two_p 19 <two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone_strict; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 21) < two_p 12) by (int auto).
  change (31 - Z.of_nat 20) with 11 in H.
  assert (12 <= d <= 31) by (int auto).
  assert ( two_p 12 <= two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
  erewrite nth_upd_neqrev; auto with zarith.
  eapply update_nth; eauto.
  rewrite Hset_eq8 in *.
  rewrite get_mpax_struct_smsh_gen with 
     (v:= ($ 201326592 >>ᵢ $ 12))
         (v1:= $ 21); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 19) by (int auto).
  change (31 - Z.of_nat (12 + 0)) with 19 in H.
  assert ( two_p 19 <two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone_strict; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 21) < two_p 12) by (int auto).
  change (31 - Z.of_nat 20) with 11 in H.
  assert (12 <= d <= 31) by (int auto).
  assert ( two_p 12 <= two_p d <= two_p 31).
  { int auto.
    eapply two_p_monotone; int auto.
    eapply two_p_monotone; int auto.
  }
  int auto.
  erewrite nth_upd_neqrev; auto with zarith.
  eapply update_nth; eauto.
  rewrite Hset_eq7 in *.
  rewrite get_mpax_struct_xmch_gen with 
     (v:= ($ 201326592 >>ᵢ $ 12))
     (v1:= $ 21); eauto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 201326592 >>ᵢ $ 12) < two_p 19) by (int auto).
  change (31 - Z.of_nat (12 + 0)) with 19 in H.
  assert ( two_p 19 <two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone_strict; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
  clear.
  intros.
  eapply Int.bits_size_2.
  eapply Z.ge_le.
  eapply Int.size_interval_2.
  int auto.
  assert (Int.unsigned ($ 21) < two_p 12) by (int auto).
  change (31 - Z.of_nat 20) with 11 in H.
  assert (12 <= d <= 31) by (int auto).
  assert ( two_p 12 <= two_p d <= two_p 31).
  { int auto.
  eapply two_p_monotone; int auto.
  eapply two_p_monotone; int auto.
  }
  int auto.
(* R_SES_Mpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply R_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply R_SES_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite update_nth; eauto.
  eapply R_SES_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_SES_Mpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
(* R_SMS_Mpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply R_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply R_SMS_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite update_nth; eauto.
  eapply R_SMS_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_SMS_Mpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
(* R_XMpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply R_XMC_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  erewrite update_nth; eauto.
  eapply R_XMC_Mpax_P_update_hold_comm'; eauto.
  solve_part_int_rgn.
(* RH_XMC_Mpax_P *)
  change (Int.ltu ($ 12) Int.iwordsize) with true.
  simpl val_inj.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  auto.
  Optimize Proof.
  Optimize Heap.
  auto.
  auto.
  Unshelve.
  all: auto.
  all: exact 0%nat.

Qed.