Require Import os_code_defs. 
Require Import code_notations. 
Require Import os_ucos_h. 
Require Import abs_op.

(* new lemmas in absop_rules *)
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import gjb_mutex_common.
Require Import os_mutex. 
Require Import os_inv.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** mutex accept **************************************) 

Lemma mutexacc_absimp_iserr:
  forall P sch s vp rv,
    can_change_aop P ->
    rv = Vint32 Int.zero ->
    absinfer sch
             ( <|| mutexacc (vp :: rv :: nil) ;; s ||> ** P)
             (<|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
  infer_solver 0%nat.
Qed.

Lemma mutexcre_absimp_iserr_abt:
  forall P sch s vp rv,
    can_change_aop P ->
    rv <> Vint32 Int.zero ->
    absinfer sch
             ( <|| mutexacc (vp :: rv :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice1; auto); eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_null:
   forall sch v' P, 
    can_change_aop P ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vnull :: v':: nil) ||> ** P)
      (<|| END (Some (Vint32 Int.zero)) ||> ** P).
Proof.
infer_solver 1%nat.
Qed.

Lemma mutexacc_absimp_null':
   forall sch v' P s, 
    can_change_aop P ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vnull :: v':: nil) ;; s ||> ** P)
      (<|| s ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 1%nat.
Qed.

Lemma mutexacc_absimp_null_abt:
   forall sch v' P, 
    can_change_aop P ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vnull :: v':: nil) ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_null_abt':
   forall sch v' P s, 
    can_change_aop P ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vnull :: v':: nil) ;; s ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

(* Lemma mutexacc_absimp_not_legal_abt:
   forall sch v' P mid els, 
    can_change_aop P ->
    get els mid = None ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_not_legal_abt':
   forall sch v' P mid els s, 
    can_change_aop P ->
    get els mid = None ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed. *)

Lemma mutexacc_absimp_wrong_type:
   forall sch v' P mid els, 
    can_change_aop P ->
    ~(exists x y wls,  get els mid = Some(absmutexsem x y, wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> ** HECBList els ** P)
      (<|| END (Some (Vint32 Int.zero)) ||> ** HECBList els ** P).
Proof.
infer_solver 2%nat.
Qed.

Lemma mutexacc_absimp_wrong_type':
   forall sch v' P mid els s, 
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some(absmutexsem x y, wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 2%nat.
Qed.

Lemma mutexacc_absimp_wrong_type_abt:
   forall sch v' P mid els, 
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some(absmutexsem x y, wls)) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_wrong_type_abt':
   forall sch v' P mid els s, 
    can_change_aop P ->
    ~(exists x y wls, get els mid = Some(absmutexsem x y, wls)) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_no_available:
   forall sch v' P mid els, 
    can_change_aop P ->
    (exists wls p o, get els mid = Some (absmutexsem p (Some o), wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> ** HECBList els ** P)
      (<|| END (Some (Vint32 Int.zero)) ||> ** HECBList els ** P).
Proof.
infer_solver 3%nat.
Qed.

Lemma mutexacc_absimp_no_available':
   forall sch v' P mid els s, 
    can_change_aop P ->
    (exists wls p o, get els mid = Some (absmutexsem p (Some o), wls)) ->
    v' = Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 3%nat.
Qed.

Lemma mutexacc_absimp_no_available_abt:
   forall sch v' P mid els p o wls, 
    can_change_aop P ->
    get els mid = Some (absmutexsem p (Some o), wls) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_no_available_abt':
   forall sch v' P mid els p o wls s, 
    can_change_aop P ->
    get els mid = Some (absmutexsem p (Some o), wls) ->
    v' <> Vint32 Int.zero ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexacc_absimp_pip_hold:
   forall sch v' P mid els pip wls tls ct pt st m t sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = true ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
infer_solver 4%nat.
Qed.

Lemma mutexacc_absimp_pip_hold':
   forall sch v' P mid els pip wls tls ct pt st m t s sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = true ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ;; s ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)) 
              by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 4%nat.
Qed.

Lemma mutexacc_absimp_pip_hold_abt:
   forall sch v' P mid els pip wls tls ct pt st m t sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = false ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)) 
              by can_change_aop_solver.
do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq; eauto).
2 : { eapply absinfer_seq_abt; try eauto. }
eapply absinfer_abt; try eauto.
absimp_abt_solver;
instantiate (3 := s);
instantiate (2:= mutexacc_pip_hold (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

Lemma mutexacc_absimp_pip_hold_abt':
   forall sch v' P mid els pip wls tls ct pt st m t s sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = false ->
    absinfer sch
      (<|| mutexacc (Vptr mid :: v':: nil) ;; s ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)) 
              by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; eauto).
2 : { eapply absinfer_seq_abt; try eauto. }
do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq; eauto).
2 : { eapply absinfer_seq_abt; try eauto. }
eapply absinfer_abt; try eauto.
absimp_abt_solver;
instantiate (3 := s0);
instantiate (2:= mutexacc_pip_hold (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

(* Lemma mutexacc_absimp_succ:
   forall sch v' P mid els pip wls tls ct pt st m t
                infol minfol qattrl semeibs muxeibs qeibs vhold
                         ebls pbls evatoms evstructs evarrays
                         tcblh tcbvl fecbh fecbvl,
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m) ->
    Int.ltu pip pt = true ->
    v'  = Vint32 Int.one ->
    absinfer sch
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct **
           ACNU infol minfol qattrl semeibs muxeibs qeibs els vhold
                         ebls pbls evatoms evstructs evarrays
                         tcblh tcbvl fecbh fecbvl ** P)
      (<|| END (Some (Vint32 Int.one)) ||> ** 
          HECBList (set els mid (absmutexsem pip (Some (ct,pt)), wls)) **
          HTCBList tls ** HTime t ** HCurTCB ct **
          ACNU infol minfol qattrl semeibs muxeibs qeibs (set els mid (absmutexsem pip (Some (ct,pt)), wls)) vhold
                         ebls pbls evatoms evstructs evarrays
                         tcblh tcbvl fecbh fecbvl ** P).
Proof.
infer_solver 0%nat.
unfold ACNU in *.
unfold AEINFO in *.
unfold AEIBAarray in *.
unfold AMqEIBAarray in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
Qed. *)
Require Import evtinv_lemmas.
Lemma mutexacc_absimp_succ':
   forall sch v' P mid els pip wls tls ct pt st m t s sus tcblh tcbvl vhold v1 v2 v3,
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = true ->
    v'  = Vint32 Int.one ->
    absinfer sch
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ;; s ||> **
           HECBList els ** 
           EvtInv_part2 els tcblh tcbvl vhold v1 v2 v3 ** HTCBList tls ** HTime t ** HCurTCB ct **  P)
      (<|| s ||> ** 
           HECBList (set els mid (absmutexsem pip (Some (ct,pt)), wls)) ** 
          EvtInv_part2 (set els mid (absmutexsem pip (Some (ct,pt)), wls)) tcblh tcbvl vhold v1 v2 v3 **
          HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
infer_solver 0%nat.
unfold EvtInv_part2 in *.
unfold ASemEIBs in *.
unfold AMuxEIBs in *.
unfold AMqEIBs in *.
sep pauto.
eapply mq_ecb_p_mux_set_preserve; eauto.
eapply mux_ecb_p_mux_set_preserve; eauto.
eapply sem_ecb_p_mutex_set_preserve; eauto.
eapply RH_SEM_EINFO_ECB_P_mux_set_preserve; eauto.
eapply RH_MUX_EIB_ECB_P_mux_set_preserve; eauto.
eapply RH_EIB_ECB_Q_P_mux_set_preserve; eauto.
Qed.

Lemma mutexacc_absimp_succ_abt:
   forall sch v' P mid els pip wls tls ct pt st m t sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = true ->
    v'  <> Vint32 Int.one ->
    absinfer sch
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)) 
              by can_change_aop_solver.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
instantiate (3 := s);
instantiate (2:= mutexacc_succ (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

Lemma mutexacc_absimp_succ_abt':
   forall sch v' P mid els pip wls tls ct pt st m t s sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip None, wls) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.ltu pip pt = true ->
    v'  <> Vint32 Int.one ->
    absinfer sch
      (<|| mutexacc_succ (|Vptr mid :: v':: nil|) ;; s ||> **
           HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> ** 
          HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)) 
              by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; eauto).
2 : { eapply absinfer_seq_abt; try eauto. }
eapply absinfer_abt; try eauto.
absimp_abt_solver;
instantiate (3 := s0);
instantiate (2:= mutexacc_succ (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

(* new in OSMutaxAcceptProof.v *)

Require Import ucos_include.
Require Import OSMutex_common.
Require Import OSTimeTickPure.
Require Import Lia.
Require Import sem_common.
Require Import sem_corecommu.
Require Import seplog_trm_tacs.
Require Import gjb_common.
Require Import gjb_mutex_common.
Require Import freeevtlist_lemmas.

Local Open Scope code_scope.

(* copy form OSMutexPend_pure_ext.v *)

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl petbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
induction els1.
intros.
tryfalse.
induction els1.
unfold get_last_ptr.
simpl.
intros.
destruct a.
destruct p. (* new add *)
destruct head;
try inverts H1.
destruct (beq_addrval qid a); try tryfalse.
destruct (V_OSEventListPtr v0 ); try tryfalse. (* v -> v0 *)
destruct v2; try tryfalse. (* v1 -> v2 *)
destruct (beq_addrval qid a0) eqn: eq1.
apply beq_addrval_eq in eq1.
subst. auto.
destruct (V_OSEventListPtr osevent); try tryfalse.
destruct v2; try tryfalse.  (* v1 -> v2 *)
intros.
destruct a.
destruct p. (* new add *)
assert (Hn: (a0 :: els1) <> nil) by pauto.
eapply (Mbox_common.get_last_prop) in Hn.
erewrite Hn.
destruct a0.
destruct p. (* new add *)
eapply IHels1; try pauto;
clear IHels0 IHels1 Hn;
simpl in *;
destruct head; try tryfalse; try auto;
destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
destruct (V_OSEventListPtr v3); try auto; try tryfalse; (* v1 -> v3 *)
destruct (V_OSEventListPtr v0); try tryfalse;  (* v -> v0 *)
destruct v6; try tryfalse;  (* v4 -> v6 *)
destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma ecblist_p_decompose_new:
  forall l1 ll1 l2 ll2 head ecbls tcbls eptr curl ecbcurl,
    length l1 = length ll1 ->
    get_ectr (Vptr eptr) head l1  = None ->
    get_ectr (Vptr eptr) head (l1 ++ (curl :: nil))  = Some curl ->
    ECBList_P head Vnull
              (l1++ (curl :: nil) ++ l2) (ll1 ++ (ecbcurl :: nil) ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2,
      ECBList_P head (Vptr eptr) l1 ll1 ecbls1 tcbls /\
      ECBList_P (Vptr eptr) Vnull ((curl :: nil) ++ l2) ((ecbcurl :: nil) ++ ll2) ecbls2 tcbls /\
      EcbMod.join ecbls1 ecbls2 ecbls /\ 
      (get_last_ptr l1 = None \/ get_last_ptr l1 = Some (Vptr eptr)).
Proof.
introv Hl Hgptr1 Hgptr2 Hep.
assert (Hl1: l1 = nil \/ l1 <> nil) by tauto.
destruct Hl1.
subst l1.
assert (ll1 = nil) by (eapply length_zero_nil; simpl in *; auto).
subst ll1.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
destruct (beq_addrval eptr x) eqn: eq1.
Focus 2.
destruct (V_OSEventListPtr v0); try tryfalse; destruct v2; try tryfalse. (*v,v1 -> v0, v2 *)
apply beq_addrval_eq in eq1.
subst x.
do 2 eexists.
splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
apply EcbMod.map_join_comm.
apply EcbMod.map_join_emp.
lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep.
simpl in *.
destruct curl.
destruct p. (* new add *)
mytac.
lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
destruct H3; rewrite H1 in Hx2; inverts Hx2.
do 2 eexists. splits; try eauto.
exists eptr. splits; try auto.
do 3 eexists. splits; eauto.
Qed.

Lemma OSMutexAccept_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSMutexAccept
                  vl logicl OSMutexAcceptPre ct->
      Some r =
      BuildRetI os_internal OSMutexAccept vl logicl OSMutexAcceptPost ct->
      exists t d1 d2 s,
        os_internal OSMutexAccept = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'1 into opv.
  change  ((x :: nil) ++ opv :: nil) with  (x :: opv :: nil).
  subst.
  inverts H0.
  rename v'0 into x.
  rename v'2 into ier.
  (* OSIntNesting *)
   hoare forward prim.
  (* splits; eauto.
  intros; splits; eauto. *)
  unfold AGVars.
(*   unfold AOSIntNesting. *)
  hoare unfold.
  hoare forward.
  pure_auto.
  hoare unfold.
  assert (Hvret: opv =Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply mutexcre_absimp_iserr_abt; eauto.
           pure_auto.
           unfold aemp_isr_is. go.
           unfold aemp_isr_is. go.
           eapply absabort_rule.
         } 
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_absimp_iserr; eauto.
  pure_auto. unfold aemp_isr_is. go.
  unfold aemp_isr_is. go.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  sep cancel p_local.
  unfold aemp_isr_is.
  sep pauto.
  pure_auto. pure_auto.
  instantiate (1:= Afalse).
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  pure_auto. pure_auto.
  clear -H1.
  (* end add *)

(*   rename H1 into Hptr. *)
  destruct H1.
  (* x = Vnull *)
  subst x.
  assert (Hopv: opv = Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto.
  destruct Hopv.
  2 :{
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutexacc_absimp_null_abt'; eauto.
        can_change_aop_solver.
        eapply absabort_rule.
  }
  subst opv.
  hoare forward prim.
  (* splits; eauto.
  intros; splits; eauto. *)
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexacc_absimp_null'; eauto.
  can_change_aop_solver.
  unfold aemp_isr_is. go.
  rewrite repr_zero.
  hoare forward prim.
  unfold aemp_isr_is.
  sep pauto.
  pure_auto. pure_auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct H1; tryfalse.
  (* x = Vptr mid *)
  destruct H as ((mid_b & mid_i) & H).
  subst x.
  hoare forward prim.
  (* splits; eauto.
  intros; splits; eauto. *)
  hoare unfold.
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  unfold EvtInv.

  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19. 

  hoare unfold.
  rename v'33 into locmp.
  rename v'34 into ptrmp.
  rename v'8 into els.
  rename v'16 into fecbh.
  rename v'17 into fecbvl.
  rename v'28 into semeibs.
  rename v'29 into muxeibs.
  rename v'30 into mqeibs.
  hoare_assert_pure (get ptrmp ct = Some (Vptr (mid_b, mid_i), Vnull, Vnull)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (evlocid, evptrid, tcbllsegevaux, AOSTCBList,p_local).
    eapply get_aux;eauto.
   }
  hoare_split_pure_all.
  destruct H3 as (Hget_ptr & Hget_loc).

  assert (Hevt: is_evt els (mid_b, mid_i) \/ ptr_in_ecblist (Vptr (mid_b, mid_i)) fecbh fecbvl).  
  { eapply mux_ecb_nml; eauto. }

  destruct Hevt as [Hevt | Hfree]. 
  Focus 2.
  (* pevent points into list of free ECBs *)
  assert (Hfecbh_eq: exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  destruct Hfecbh_eq as ( (fb & fi) & Heq).
  subst fecbh.
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.
  hoare forward.
  go.
  2: { instantiate(1:= Afalse).
          eapply hoare_disj_afalseP_l_pre.
          change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_MUTEX)) with false. 
          hoare unfold.
          simpl in H3; change (Int.notbool Int.zero) with Int.one in H3; 
          destruct H3; tryfalse. }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'34, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H3 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H14 into Hnone.

   assert (Htype_err': ~ (exists x y z, get els (v'34, Int.zero) = Some (absmutexsem x y, z))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mz & Hf ); inverts Hf.
  }

  assert (Hopv: opv = Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexacc_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver.
        unfold aemp_isr_is. go.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  subst opv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexacc_absimp_wrong_type'; eauto.
  can_change_aop_solver.
  unfold aemp_isr_is. go.
  eapply absinfer_eq.
  (* EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel Aier.
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold EvtInv.
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList.
  sep cancel evsllseg.
  sep split; eauto.
  sep cancel tcbdllflag.
  sep cancel p_local.
(*   unfold ACNU. *)
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep pauto; eauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  unfolds; simpl; auto.
  go.
  pure_auto.
  pure_auto.
  (* return 0 *) 
  hoare forward.

  (* pevent points to an active ECB *) 
  assert (Hget: exists ecb, get els (mid_b, mid_i) = Some ecb).
  { clear -Hevt.
    unfold is_evt in Hevt.
    destruct Hevt as [Hsem | [Hmux | Hque]].
    unfold is_sem in Hsem.
    simpljoin1; eexists; eauto.
    unfold is_mux in Hmux.
    simpljoin1; eexists; eauto.
    unfold is_que in Hque.
    simpljoin1; eexists; eauto.
  }
  destruct Hget as (d & Hget).
(*   destruct d.  *)
  (* split AECBList *)
  unfold AECBList.
  hoare unfold.
  lets Hget_ectr: ECBList_P_get_ectr_some Hget H3.
  destruct Hget_ectr as (et & etbl & petbl & Hget_ectr).
  eapply backward_rule1.
  intros.
  eapply get_ectr_decompose; eauto.
  sep cancel evsllseg. eauto.
  hoare unfold.
  hoare_assert_pure (length v'16 = length v'28).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'8).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose_new H11 H25 H26 H3.
  mytac.
  simpl ECBList_P at 1 in H15.
  mytac.
  inverts H15.
  (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_MUTEX*)
  hoare forward.
  go.
  pure_auto.
  pure_auto.
  hoare unfold.
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  simpl in H15. change (Int.notbool Int.one) with Int.zero in H15. tryfalse.

  eapply backward_rule1.
  intros.
  eapply eventtype_neq_mutex; eauto.
  sep cancel AEventData. eauto.
  hoare_split_pure_all.
  rename H36 into Htype_err.
(*   assert (Htype_err': ~ (exists x y z, d = (absmutexsem x y, z))).
  {
   clear -Hget Htype_err.
   rewrite Hget in Htype_err.
   pure_auto.
  eapply Htype_err.
  mytac.
  eauto.
  } *)

  assert (Hopv: opv = Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexacc_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver.
        unfold aemp_isr_is. go.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  subst opv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexacc_absimp_wrong_type'; eauto.
  can_change_aop_solver.
  unfold aemp_isr_is. go.
  eapply absinfer_eq.
  hoare forward prim.
  unfold EvtInv.
  sep cancel tcbdllflag.
  unfold AECBList.
  sep pauto; eauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  eapply evsllseg_compose;eauto.
  unfolds; simpl; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  split; auto. go.
  pure_auto. go.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
   (* OSEventType = OS_EVENT_TYPE_MUTEX *)
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  2: { simpl in H15. change (Int.notbool Int.zero) with Int.one in H15.
          destruct H15; tryfalse. }
  eapply inteqeq in eq1.
  subst i1.
  destruct v'30;
  [ simpl AEventData | simpl AEventData | simpl AEventData | idtac | simpl AEventData];
  hoare unfold.
  hoare_assert_pure (DMutex v v0 = DMutex (Vint32 i2) x0).
  { get_hsat Hsat.
    simpl AEventData in Hsat.
    sep split in Hsat.
    inverts H40. inverts H41. auto.
  }
  hoare_split_pure_all.
  inverts H36.
  destruct x5.
  lets Hcp: H38.
  destruct e; simpl in H38; tryfalse.
  mytac.
  funfold H36.
  inverts H36.
  assert (Hget': get els (v'37,Int.zero) = Some (absmutexsem (x3 >>ᵢ $ 8) o, w)).
  {
    eapply EcbMod.join_get_r; eauto.
    eapply EcbMod.join_sig_get; eauto.
  }
   assert (Hif_cond: x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE 
                                        \/ x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE ) by tauto.
  destruct Hif_cond as [Hif_true | Hif_false].
  (* Hif_false *)
  2: {
        lets Heq: Int.eq_false Hif_false.
        lets Hget_o: H47 Hif_false.
        mytac.
        hoare forward.
        go. pure_auto.
        rewrite Heq.
        simpl val_inj.
        hoare_unfold. tryfalse.
        instantiate (1:= Afalse).
         eapply hoare_disj_afalseP_l_pre.
        hoare_split_pure_all.
        assert (Hopv: opv = Vint32 Int.zero \/ opv <> Vint32 Int.zero) by tauto.
        hoare_lifts_trms_pre (Aop, absecblsid).
        destruct Hopv.
        subst opv.
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexacc_absimp_no_available'; eauto.
        can_change_aop_solver.
        unfold aemp_isr_is. go.
        eapply absinfer_eq.
        hoare forward prim.
        unfold EvtInv.
        sep cancel tcbdllflag.
        unfold AECBList.
        sep pauto; eauto.
        sep cancel ASemEIBs.
        sep cancel AMuxEIBs.
        sep cancel AMqEIBs.
        sep cancel p_local.
        eapply evsllseg_compose;eauto.
        unfold V_OSEventListPtr; simpl; eauto.
        unfold AEventNode.
        unfold AOSEvent.
        unfold node.
        unfold AOSEventTbl.
        sep pauto; eauto.
        split; auto. go.
        pure_auto. go.
        hoare forward.
        (* opv <> Vint32 Int.zero*)
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexacc_absimp_no_available_abt'; eauto.
        can_change_aop_solver. unfold aemp_isr_is. go.
        eapply absinfer_eq.
        apply absabort_rule.
      }
      (* Hif_true *)
        lets Hget_o: H46 Hif_true.
        mytac.
         hoare forward.
        go. pure_auto.
        2 : {
         instantiate (1:= Afalse).
         eapply hoare_disj_afalseP_l_pre.
        rewrite Hif_true.
        rewrite Int.eq_true.
        simpl val_inj.
        hoare_split_pure_all. destruct H18; tryfalse.
        }
        hoare unfold.
        clear H18 H36 H44.
        lets Hget_t: H0.
        unfold RH_CurTCB in Hget_t.
       destruct Hget_t as (pt & st & m & sus & Hget_t).
       assert (Hpip: Int.ltu (x3 >>ᵢ $ 8) pt = true \/ Int.ltu (x3 >>ᵢ $ 8) pt = false).
        { clear -H. int auto. }
        hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid,    ostmid, curtid).
        destruct Hpip as [Hpip | Hpip_abt].
        2 :{
              eapply abscsq_rule.
              apply noabs_oslinv.
              eapply mutexacc_absimp_pip_hold_abt'; eauto.
              can_change_aop_solver. unfold aemp_isr_is. go.
              eapply absinfer_eq.
              apply absabort_rule.
        }
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexacc_absimp_pip_hold'; eauto.
        can_change_aop_solver. unfold aemp_isr_is. go.
        eapply absinfer_eq.
        (* start assign *)
        hoare forward.
        go.
        lets H_range: acpt_int_lemma0 H24.
        unfold AOSTCBList.
        hoare unfold.
        hoare forward.
        go.
        go.
        hoare forward.
        assert (Hopv: opv = Vint32 Int.one \/ opv <> Vint32 Int.one) by tauto.
        hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid,    ostmid, curtid).
        destruct Hopv.
        2: {
              eapply abscsq_rule.
              apply noabs_oslinv.
              eapply mutexacc_absimp_succ_abt'; eauto.
              can_change_aop_solver. unfold aemp_isr_is. go.
              eapply absinfer_eq.
              apply absabort_rule.
              }
(*            eapply backward_rule1.  *)
(*            introv Hsat.
           sep_lifts_trms_in Hsat (eblsid, AErrblkList, pblsid, APosblkList,
                                                   evatomheapid,AEvAtomHeap,evstructheapid,AEvStructHeap, evarrayheapid,AEvArrayHeap,
                                                   seminfoid, AEINFO, absmutinfoid, AEIBAarray, absmqattrid,AMqEIBAarray,
                                                   evlocid, evptrid, tcbllsegevaux). 
  match type of Hsat with
    _ |= Hebls ?ebls ** AErrblkList ?ebls ** Hpbls ?pbls ** _ **
            HEvAtomHeap ?evatoms ** AEvAtomHeap ?evatoms **
            HEvStructHeap ?evstructs ** AEvStructHeap ?evstructs **
            HEvArrayHeap ?evarrays ** AEvArrayHeap ?evarrays **
            HSEMInfo ?semifo ** AEINFO ?infol ?semeibs ?ecbls ?vhold **
            HMuxInfo ?muxifo ** AEIBAarray ?minfol ?meibs _ _ ** 
            HQAttr ?mqattr ** AMqEIBAarray ?qattrl ?qeibs _ _ **
            HEvLoc ?locmp ** HEvPtr ?ptrmp ** tcbllsegevaux ?tcblh ?vl _ _ ** ?Q =>
    instantiate (1 := ACNU infol minfol qattrl semeibs meibs qeibs ecbls vhold
                                                     ebls pbls evatoms evstructs evarrays
                                                    tcblh vl fecbh fecbvl  ** Q)
  end. *)
  
(*   sep auto. 
  unfold ACNU.
  sep pauto; eauto. *)
           subst opv.
      eapply backward_rule1.  
      introv Hsat.
      eapply fold_EvtInv_part2 with (s:= s); eauto.
      sep pauto.
      sep cancel ASemEIBs.
      sep cancel AMuxEIBs.
      sep cancel AMqEIBs.
      sep cancel tcbllsegevaux. eauto.
(*       sep_lifts_trms_in Hsat (AOSEventFreeList, eblsid, AErrblkList, pblsid, APosblkList,
                                                   evatomheapid,AEvAtomHeap,evstructheapid,AEvStructHeap, evarrayheapid,AEvArrayHeap,
                                                   seminfoid, ASemEIBs, absmutinfoid, AMuxEIBs, absmqattrid,AMqEIBs,
                                                   evlocid, evptrid, tcbllsegevaux).  *)
      hoare_lifts_trms_pre (Aop, absecblsid, EvtInv_part2, abstcblsid).
           eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexacc_absimp_succ'; eauto.
           can_change_aop_solver. unfold aemp_isr_is. go.
           eapply absinfer_eq.
           (*EXIT_CRITICAL*)
         hoare forward prim.
          sep cancel tcbdllflag.
          sep_lifts_trms (EvtInv).
          eapply fold_EvtInv_frm; eauto.
          sep cancel EvtInv_part2.
          sep cancel p_local.
          unfold EvtInv_part1.
          unfold AOSTCBList.
          unfold tcbdllseg.
          unfold V_OSTCBPrev,V_OSTCBNext.
          sep pauto; eauto.
          sep cancel (dllseg v'1).
          simpl dllseg.
          unfold node.
          sep pauto.
          sep cancel dllseg.
          2:{ split; eauto. go. }
          sep cancel (Astruct (v'36, Int.zero)).
          unfold AECBList.
          sep pauto.
          eapply evsllseg_compose; eauto.
          2: { sep cancel (evsllseg v'8).
(*                   sep cancel 5%nat 2%nat. *)
                  sep cancel evsllseg.
                  unfold AEventNode.
                  unfold AOSEvent.
                  unfold AOSEventTbl.
                  unfold node.
                  sep pauto; auto.
                  sep cancel Astruct.
                  sep cancel Aarray.
                  sep cancel AOSPostEventTbl.
                  sep cancel AOSQFreeList.
                  sep cancel AOSQFreeBlk.
                  sep cancel Aier.
                    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
                  instantiate (2:=  DMutex  (Vint32 (Int.or (x3&ᵢ $ OS_MUTEX_KEEP_UPPER_8) i5)) (Vptr (v'36, Int.zero))).
                  simpl AEventData in *.
                  unfold V_OSEventType,V_OSEventCnt,V_OSEventPtr.
                  sep pauto.
                  cancel_corecommuinv. 
                  
                  (* PartitionInv *)
                  Require Import sem_partition.
                  cancel_partitioninv.
                  eauto.
                  (* end of PartitionInv *)
                  
                  simpl; auto.
                  eauto.
                  unfolds; simpl; eauto.
                  auto.
                  eauto.
                  unfold V_OSEventGrp; simpl; auto.
                  auto.
                  auto.
                  split; auto.
                  assert (Hor_range: Int.unsigned (Int.or (x3&ᵢ $ OS_MUTEX_KEEP_UPPER_8) i5) <= 65535).
                  eapply acpt_intlemma6. auto with zarith.
                  go.
              }
            unfold V_OSEventListPtr; simpl ;auto.
            lets Hget_t': Mbox_common.TCBListP_head_in_tcb H45.
            destruct Hget_t' as (st' & sus' & Hget_t').
            eapply TcbMod.join_get_r in Hget_t'; eauto.
            unfold get in Hget_t. unfold TcbMap in Hget_t.
            rewrite Hget_t in Hget_t'. inverts Hget_t'.
            lets Htcb_rl: TCBList_P_imp_RL H45.
            simpl RL_TCBblk_P_List in Htcb_rl.
            destruct Htcb_rl as (Htcb_rl1 & _).
            eapply ecblist_p_compose'; 
            try eapply RLH_ECBData_p_high_mbox_acpt_hold; eauto.
            eapply tcbblk_prio_range; eauto.
            eapply ecb_sig_join_sig'_set; eauto.
            assert (Hor_eq: Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) i5 >>ᵢ $ 8 = x3 >>ᵢ $ 8).
            {
              eapply acpt_intlemma4; eauto.
              eapply tcbblk_prio_range; eauto.
          }
            rewrite Hor_eq.
            eapply EcbMod.join_set_r;eauto.
            unfolds.
            eexists.
            eapply EcbMod.join_sig_get; eauto.

           (* eapply RH_ECBlk_EIBlk_Mux_P_set_op; eauto.
           eauto.
            split;auto. go.
           eauto.
           eauto.
           eauto. *)
           assert (Hw: w = nil) by (apply H38; auto).
            subst w.
            eapply mutex_acpt_rh_tcblist_ecblist_p_hold; eauto.

            pure_auto.
            (* end of EXIT_CRITICAL *)
            eapply rete_rule.
            split; [idtac | sep get rv].
            sep normal.
            exists (Vptr (v'37, Int.zero)) v' (Vptr (v'37, Int.zero)) (Vint32 Int.one) Int.one.
            sep auto.
            simpl; introv Hf; inverts Hf.
            (* hoare forward.
            change (V$ 1) with (Vint32 Int.one).
            splits; auto. *)
Qed.

