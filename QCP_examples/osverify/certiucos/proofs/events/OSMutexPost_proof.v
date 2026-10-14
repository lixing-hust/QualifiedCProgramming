 Require Import os_code_defs. 
Require Import code_notations. 
Require Import os_ucos_h. 
Require Import os_mutex.
Require Import abs_op.

(* new lemmas in absop_rules *)
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import abs_infer_abt.
Require Import gjb_mutex_common.
Require Import gjb_common.
Require Import OSMutexPost_pure_ext.
Require Import os_inv.
Require Import evtinv_lemmas.
Require Import sem_corecommu.
Require Import hoare_forward_tac_ext.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** mutex post **************************************) 

Lemma mutexpost_absimp_null':
   forall sch v' P s, 
    can_change_aop P ->
    v' = V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vnull :: v':: nil)) s ||> ** P)
      (<|| s ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
simpl.
infer_solver 0%nat.
Qed.

Lemma mutexpost_absimp_null_abt':
   forall sch v' P s, 
    can_change_aop P ->
    v' <> V$ OS_ERR_PEVENT_NULL ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vnull :: v':: nil)) s ||> ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
simpl.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpost_absimp_wrong_type':
   forall sch v' P mid els s, 
    can_change_aop P ->
    ~(exists x y wls, get els mid  = Some (absmutexsem x y, wls)) ->
    v' = V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vptr mid :: v':: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P).
Proof.
intros.
simpl.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 2%nat.
Qed.

Lemma mutexpost_absimp_wrong_type_abt':
   forall sch v' P mid els s, 
    can_change_aop P ->
    ~(exists x y wls,  get els mid =Some (absmutexsem x y, wls)) ->
    v' <> V$ OS_ERR_EVENT_TYPE ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vptr mid :: v':: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** P)) by can_change_aop_solver.
simpl.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma mutexpost_absimp_owner_hold_abt':
   forall sch v' P mid els tls ptls pr wl o s, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pr o, wl) ->
  ~((o = None ) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy,m,false)
                                                            /\ (prio = op 
                                                                  \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder)
                                                                        /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls))))))) ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls ** HPriotls ptls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
instantiate(3:= s0);
instantiate (2:= mutexpost_owner_hold (|Vptr mid :: v' :: nil|));
sep pauto.
eapply absinfer_eq; eauto.
Qed.

Lemma mutexpost_absimp_owner_hold':
   forall sch v' P mid els tls ptls pr wl o s, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pr o, wl) ->
  ((o = None ) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy,m,false)
                                                            /\ (prio = op
                                                                  \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder)
                                                                         /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls))))))) ->
    absinfer sch
      (<|| spec_code_cons (mutexpost (Vptr mid :: v':: nil)) s ||> ** HECBList els ** HTCBList tls ** HPriotls ptls ** P)
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> ** HECBList els ** HTCBList tls ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq_end; eauto).
eapply absinfer_seq; eauto.
infer_solver 0%nat.
Qed.

Lemma mutexpost_absimp_no_owner_err':
   forall sch v' P mid els tls t ct pr wl s, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pr None, wl) ->
   prio_available pr tls ->
    v' = V$ OS_ERR_NOT_MUTEX_OWNER ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct  ** P)
      (<|| s ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct (* ** HPriotls ptls  *)** P)) by can_change_aop_solver.
simpl.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 0%nat.
Qed.

Lemma mutexpost_absimp_no_owner_abt':
   forall sch v' P mid els tls t ct pr wl s , 
    can_change_aop P ->
   get els mid = Some (absmutexsem pr None, wl) ->
   prio_available pr tls ->
   v' <> V$ OS_ERR_NOT_MUTEX_OWNER ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct  ** P)) by can_change_aop_solver.
simpl.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
try instantiate (4 := s0);
try instantiate (3 := s0);
try instantiate (3:= mutexpost_no_owner_err (|Vptr mid :: v' :: nil|));
try instantiate (2:= mutexpost_no_owner_err (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

Lemma mutexpost_absimp_not_owner_err':
   forall sch v' P mid els tls t ct pr ot op wl prio st m s sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pr (Some (ot,op)), wl) ->
   get tls ot = Some (prio, st, m, sus) ->
   prio = pr \/ prio = op ->
    ct <> ot ->
    v' = V$ OS_ERR_NOT_MUTEX_OWNER ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)
      (<||s ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct **  P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)) by can_change_aop_solver.
simpl.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 1%nat.
Qed.

Lemma mutexpost_absimp_not_owner_err_abt':
    forall sch v' P mid els tls t ct pr ot op wl prio st m s sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pr (Some (ot,op)), wl) ->
    get tls ot = Some (prio, st, m, sus) ->
    prio = pr \/ prio = op ->
    ct <> ot ->
    v' <> V$ OS_ERR_NOT_MUTEX_OWNER  ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)) by can_change_aop_solver.
simpl.
(* do 4 *) (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
try instantiate (4 := s0);
try instantiate (3 := s0);
try instantiate (3:= mutexpost_not_owner_err (|Vptr mid :: v' :: nil|));
try instantiate (2:= mutexpost_not_owner_err (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

Lemma mutexpost_absimp_nowt_return_prio_succ':
   forall sch v' P mid els tls t ct st m pip op s ptls sus, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), nil) ->
   get tls ct = Some (pip,st,m,sus) ->
    v' = V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls  ** P)
      (<|| s ||> **
      HECBList (set els mid (absmutexsem pip None, nil)) ** 
      HTCBList (set tls ct (op, st, m, sus)) **HTime t ** HCurTCB ct ** HPriotls (set (set ptls op (Valid_Addr ct)) pip Holder ) ** P).
Proof.
intros.
assert (Hc : forall els tls, can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** P)) 
            by (intros; can_change_aop_solver).
simpl.
infer_solver 2%nat.
eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
Qed.

Lemma mutexpost_absimp_nowt_return_prio_succ_abt':
   forall sch v' P mid els tls t ct st m pip op s ptls sus, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), nil) ->
   get tls ct = Some (pip,st,m,sus) ->
    v' <> V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
try instantiate (3 := s0);
try instantiate (4 := s0);
try instantiate (2:= mutexpost_nowt_return_prio_succ (|Vptr mid :: v' :: nil|));
try instantiate (3:= mutexpost_nowt_return_prio_succ (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

Lemma mutexpost_absimp_nowt_no_return_prio_succ':
   forall sch v' P mid els tls t ct st m pip op s pt ptls sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip (Some (ct, op)), nil) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.eq pt pip = false ->
    v' = V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| s ||> **
      HECBList (set els mid (absmutexsem pip None, nil)) ** 
      HTCBList tls **HTime t ** HCurTCB ct  ** HPriotls (set ptls pip Holder) ** P).
Proof.
intros.
assert (Hc : forall els tls, can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)) 
            by (intros; can_change_aop_solver).
simpl.
infer_solver 3%nat.
Qed.

Lemma mutexpost_absimp_nowt_no_return_prio_succ_abt':
   forall sch v' P mid els tls t ct st m pip op s pt ptls sus, 
    can_change_aop P ->
    get els mid = Some (absmutexsem pip (Some (ct, op)), nil) ->
    get tls ct = Some (pt,st,m,sus) ->
    Int.eq pt pip = false ->
    v' <> V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver;
try instantiate (3 := s0);
try instantiate (4 := s0);
try instantiate (2:= mutexpost_nowt_no_return_prio_succ (|Vptr mid :: v' :: nil|));
try instantiate (3:= mutexpost_nowt_no_return_prio_succ (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.

(*-------------------------------------------------------------------------------------------------------------------- *)

Lemma mutexpost_absimp_wl_highest_prio_err_abt':
   forall sch v' P mid els tls ct st m pip op wl t' pw s sus, 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), wl) ->
    wl <> nil ->
    GetHWait tls wl t' ->
   get tls t' = Some (pw,st,m,sus) ->
    Int.ltu pip pw = false ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls ** P)) by can_change_aop_solver.
do 4 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_abt; try eauto.
absimp_abt_solver';
instantiate (3 := s0);
instantiate (2:= mutexpost_wl_highest_prio_err (|Vptr mid :: v' :: nil|));
sep pauto.
Qed.


(* -------------------------------------------------------------------------------------------------------------------  *)

Lemma mutexpost_absimp_exwt_return_prio_succ':
   forall sch v' P mid els tls t ct st m pip op wl t' p' st' m' s ptls sus sus', 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), wl) ->
    wl <> nil ->
    GetHWait tls wl t' ->
   get tls ct = Some (pip,st,m,sus) ->
   get tls t' = Some (p',st',m',sus') ->
    v' = V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| isched;; END (Some (V$ OS_NO_ERR)) ;; s ||> **
      HECBList (set els mid (absmutexsem pip (Some (t', p')), remove_tid t' wl)) ** 
      HTCBList (set (set tls ct (op, st, m, sus)) t' (p', rdy, Vnull, sus')) **HTime t ** HCurTCB ct ** HPriotls (set (set ptls op (Valid_Addr ct)) pip Holder) ** P).
Proof.
simpl spec_code_cons. 
try match goal with
        | |- context [ <|| ?x _ ||> ] => unfold x
      end; intros.
infer_branch 5%nat.
eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver.
Focus 3.
apply absinfer_seq_end.
2: can_change_aop_solver.
Focus 2.
intro.
intros.
eauto.
can_change_aop_solver.
can_change_aop_solver.
infer_part1 0%nat.
assert (Hex: exists x,  get (set tls ct (op, st, m, sus)) t' = Some x).
{ rewrite TcbMod.set_sem.
  destruct (tidspec.beq ct t') eqn: eq; eauto. }
destruct Hex as (x & Hex).
infer_part2.
eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
Qed.

Lemma mutexpost_absimp_exwt_return_prio_succ_abt':
   forall sch v' P mid els tls t ct st m pip op wl t' p' st' m' s ptls sus sus', 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), wl) ->
    wl <> nil ->
    GetHWait tls wl t' ->
   get tls ct = Some (pip,st,m,sus) ->
   get tls t' = Some (p',st',m',sus') ->
    v' <> V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
do 5 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver';
(* absimp_abt_solver; *)
try instantiate (3 := s0);
try instantiate (4 := s0);
try instantiate (2:= mutexpost_exwt_return_prio_succ (|Vptr mid :: v' :: nil|));
try instantiate (3:= mutexpost_exwt_return_prio_succ (|Vptr mid :: v' :: nil|));
try sep pauto.
Qed.

(* -------------------------------------------------------------------------------------------------------------------  *)
Lemma mutexpost_absimp_exwt_no_return_prio_succ':
   forall sch v' P mid els tls t ct st m pip op wl t' p' st' m' cp s ptls sus sus', 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), wl) ->
    wl <> nil ->
    GetHWait tls wl t' ->
    Int.eq cp pip = false ->
   get tls ct = Some (cp,st,m,sus) ->
   get tls t' = Some (p',st',m',sus') ->
    v' = V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| isched;; END (Some (V$ OS_NO_ERR)) ;; s ||> **
      HECBList (set els mid (absmutexsem pip (Some (t', p')), remove_tid t' wl)) ** 
      HTCBList (set tls t' (p', rdy, Vnull,sus')) **HTime t ** HCurTCB ct ** HPriotls (set ptls pip Holder) ** P).
Proof.
simpl spec_code_cons. 
try match goal with
        | |- context [ <|| ?x _ ||> ] => unfold x
      end; intros.
infer_branch 5%nat.
eapply absinfer_trans.
eapply absinfer_seq.
can_change_aop_solver.
Focus 3.
apply absinfer_seq_end.
2: can_change_aop_solver.
Focus 2.
intro.
intros.
eauto.
can_change_aop_solver.
can_change_aop_solver.
infer_solver 1%nat.
eapply tidsame_trans; [idtac | eapply tidsame_set;eauto].
eapply tidsame_trans; repeat try eapply tidsame_set; eauto.
Qed.

Lemma mutexpost_absimp_exwt_no_return_prio_succ_abt':
   forall sch v' P mid els tls t ct st m pip op wl t' p' st' m' cp s ptls sus sus', 
    can_change_aop P ->
   get els mid = Some (absmutexsem pip (Some (ct, op)), wl) ->
    wl <> nil ->
    GetHWait tls wl t' ->
    Int.eq cp pip = false ->
   get tls ct = Some (cp,st,m,sus) ->
   get tls t' = Some (p',st',m',sus') ->
    v' <> V$ OS_NO_ERR ->
    absinfer sch
      (<|| spec_code_cons (mutexpost_aft_owner (Vptr mid :: v':: nil)) s ||> **
        HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)
      (<|| ABORT ||> **
      HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P).
Proof.
intros.
assert (Hc : can_change_aop (HECBList els ** HTCBList tls **HTime t ** HCurTCB ct ** HPriotls ptls ** P)) by can_change_aop_solver.
simpl.
do 5 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
eapply absinfer_seq; eauto.
eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver';
(* absimp_abt_solver; *)
try instantiate (3 := s0);
try instantiate (4 := s0);
try instantiate (2:= mutexpost_exwt_no_return_prio_succ (|Vptr mid :: v' :: nil|));
try instantiate (3:= mutexpost_exwt_no_return_prio_succ (|Vptr mid :: v' :: nil|));
try sep pauto.
Qed.

(* new in OSMutexPostProof.v *)

Require Import ucos_include.
Require Import OSMutex_common.
Require Import OSTimeTickPure.
Require Import OSMutexPostPure. 
(* Require Import os_ucos_h. *)
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import sem_lab.
Require Import OSQPostPure.
(* Require Import tcblist_setnode_lemmas. *)
Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Lemma mutexpost_absimp_iserr:
  forall P sch s vp rv,
    can_change_aop P ->
    rv = Vint32 (Int.repr OS_ERR_POST_ISR) ->
    absinfer sch
             ( <|| spec_code_cons (mutexpost (vp :: rv :: nil)) s ||> ** P)
             (<|| END Some (V$ OS_ERR_POST_ISR) ;; s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
  instantiate (1:= END (Some (V$ OS_ERR_POST_ISR)) ).
simpl spec_code_cons.
  infer_solver 0%nat. eapply absinfer_eq.
Qed.

 Lemma mutexpost_absimp_iserr_abt:
  forall P sch s vp rv,
    can_change_aop P ->
    rv <> Vint32 (Int.repr OS_ERR_POST_ISR)->
    absinfer sch
             ( <|| spec_code_cons (mutexpost (vp :: rv :: nil)) s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
  simpl spec_code_cons.
  eapply absinfer_trans; try (eapply absinfer_choice1; auto); eauto.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto. 
  eapply absinfer_seq; eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed. 

Lemma mutexpost_absimp_iserr_end:
  forall P sch s,
    can_change_aop P ->
    absinfer sch
             ( <|| END Some (V$ OS_ERR_POST_ISR) ;; s ||> ** P)
             (<|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq_end; try eauto).
  eapply absinfer_eq.
Qed.

(* Lemma tcb_stat_imp_sus_false:
forall vl rtbl p st m sus stat,
   R_TCB_Status_P vl rtbl (p, st, m, sus) ->
   V_OSTCBStat vl = Some (Vint32 stat) ->
   (stat =$ OS_STAT_RDY \/ stat = ($ OS_STAT_SEM) \/
   stat = ($ OS_STAT_Q) \/ stat = ($ OS_STAT_POSTQ) \/
   stat = ($ OS_STAT_MUTEX) \/ stat = ($ OS_STAT_MBOX)) ->
   sus = false.
Proof.
  intros.
  destruct sus; auto.
  eapply tcb_stat_sus_true_imp_stat_gen in H.
  simpljoin.
  rewrite H0 in H; inverts H.
  destruct H1 as [ H | [ H | [ H | [ H | [ H | H ]]]]]; subst;
  destruct H2 as [ H | [ H | [ H | [ H | [ H | H ]]]]]; tryfalse.
Qed. *)

Require Import evauxvar_lemmas.
Require Import evaux_pure.

Open Scope int_scope.
Open Scope Z_scope.
 Require Import hoare_forward_tac_ext.
Open Scope code_scope.
Lemma OSMutexPost_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSMutexPost vl logicl OSMutexPostPre ct->
      Some r =
      BuildRetI os_internal OSMutexPost vl logicl OSMutexPostPost ct->
      exists t d1 d2 s,
        os_internal OSMutexPost = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'2 into opv.
  rename v'4 into ier.
  change  ((x :: nil) ++ opv :: nil) with  (x :: opv :: nil).
  subst.

  (* OSIntNesting *)
   hoare forward prim.
  unfold AGVars.
  hoare unfold.
  hoare forward.
  pure_auto.
  hoare unfold.
  assert (Hvret: opv =Vint32 (Int.repr OS_ERR_POST_ISR) \/ opv <> Vint32 (Int.repr OS_ERR_POST_ISR)) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply mutexpost_absimp_iserr_abt; eauto.
           pure_auto. 
           eapply absabort_rule.
         } 
  subst. 
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexpost_absimp_iserr; eauto.
  pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto. auto.
  pure_auto.
  instantiate (1:= Afalse).
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexpost_absimp_iserr_end; eauto.
  pure_auto.
  hoare forward.
  2:{ splits; eauto. unfold OS_ERR_POST_ISR; int auto.
  change (Byte.max_unsigned) with 255.
  unfold OS_ERR_POST_ISR; int auto. }
  unfold OS_ERR_POST_ISR. intros. int auto.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto. auto.
  pure_auto.
  clear -H1.

(*   rename H1 into Hptr. *)
  rename v'3 into x.
  destruct H1.
  
  (* x = Vnull *)
  subst x.
  assert (Hopv: opv = V$ OS_ERR_PEVENT_NULL \/ opv <> V$ OS_ERR_PEVENT_NULL ) by tauto.
  destruct Hopv.
  2 :{
        hoare abscsq.
        apply noabs_oslinv.
        eapply mutexpost_absimp_null_abt'; eauto.
        can_change_aop_solver.
        eapply absabort_rule.
  }
  subst opv.
  hoare forward prim.
  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutexpost_absimp_null'; eauto.
  can_change_aop_solver.
  hoare forward prim.
  sep pauto. auto.
  pure_auto.
  hoare forward.
  2:{ splits; eauto;
  unfold OS_ERR_PEVENT_NULL; int auto.
  change Byte.max_unsigned with 255. auto with zarith. }
  intros.  unfold OS_ERR_PEVENT_NULL; int auto.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct H1; tryfalse.
  (* x = Vptr mid *)
  destruct H as ((mid_b & mid_i) & H).
  subst x.
  hoare forward prim.
  hoare unfold.
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  unfold EvtInv.
  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 

  hoare unfold.
  rename v'35 into locmp.
  rename v'36 into ptrmp.
  rename v'10 into els.
  rename v'18 into fecbh.
  rename v'19 into fecbvl.
  rename v'30 into semeibs.
  rename v'31 into muxeibs.
  rename v'32 into mqeibs.
  hoare_assert_pure (get ptrmp ct = Some (Vptr (mid_b, mid_i), Vnull, Vnull)
                                             /\ get locmp ct = Some (V$ os_code_defs.__EvLoc_normal)).
  { get_hsat Hsat.
Require Import seplog_trm_tacs.
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
Require Import freeevtlist_lemmas.
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

  (*if OSEventType !=ₑ ′ OS_EVENT_TYPE_MUTEX*)
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

  hoare_assert_pure (get els (v'36, Int.zero) = None).
  {
    get_hsat Hsat. 
  Require Import sem_common.
    lets H00: semcre_ecblist_star_not_inh H3 Hsat.
    auto.
  }
  hoare_split_pure_all.
  rename H14 into Hnone.

   assert (Htype_err': ~ (exists x y z, get els (v'36, Int.zero) = Some (absmutexsem x y, z))).
  { rewrite Hnone.
    introv Hf; destruct Hf as (mx & my & mz & Hf ); inverts Hf.
  }

  assert (Hopv: opv = V$ OS_ERR_EVENT_TYPE \/ opv <> V$ OS_ERR_EVENT_TYPE) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpost_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpost_absimp_wrong_type'; eauto.
  can_change_aop_solver. eapply absinfer_eq.
  hoare forward prim.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold AOSEventFreeList.
  sep pauto.
  sep cancel evsllseg.
  unfold ecbf_sll.
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.
  eauto.
  unfolds; simpl; auto.
  go. go. eauto. eauto. eauto. eauto. auto.
  pure_auto.
  hoare forward.
hoare unfold.

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
  hoare_assert_pure (length v'18 = length v'30).
  { get_hsat Hsat. sep_lifts_trms_in Hsat (evsllseg v'10).
     eapply evsllseg_list_len_eq in Hsat; auto.
  }
  hoare_split_pure_all.
  lets Hels_split: ecblist_p_decompose_new H11 H25 H26 H3.
  mytac.
  simpl ECBList_P at 1 in H15.
  mytac.
  inverts H15.

  hoare forward.   go.
  pure_auto.
  pure_auto.
  hoare unfold.
   (* OSEventType = OS_EVENT_TYPE_MUTEX *)
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  simpl in H15. change (Int.notbool Int.one) with Int.zero in H15. tryfalse.
  eapply backward_rule1.
  intros.
  eapply eventtype_neq_mutex; eauto.
  sep cancel AEventData. eauto.
  hoare_split_pure_all.
  rename H36 into Htype_err.
  assert (Hopv: opv = V$ OS_ERR_EVENT_TYPE \/ opv <> V$ OS_ERR_EVENT_TYPE) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid).
  destruct Hopv.
  2 :{
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpost_absimp_wrong_type_abt'; eauto.
        can_change_aop_solver. eapply absinfer_eq.
        eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpost_absimp_wrong_type'; eauto.
  can_change_aop_solver. eapply absinfer_eq.
  hoare forward prim.
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  eapply evsllseg_compose;eauto. 
  instantiate (2:= (Vint32 i1
            :: Vint32 i0
               :: Vint32 i2
                  :: x0
                     :: x1 :: x7 :: Vint32 i :: x4 :: nil)). eauto. 
  unfolds; simpl; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto. 
  sep cancel Astruct.
  sep cancel AEventData.
  sep cancel AOSPostEventTbl.
  sep cancel Aarray.
  sep pauto. eauto. eauto. eauto. eauto.
  eauto. eauto. eauto.
  split; auto. go. auto. auto. auto.
  pure_auto. pure_auto. pure_auto.
  instantiate (1:= Afalse).
  hoare forward.
  2:{ splits; eauto; unfold OS_ERR_EVENT_TYPE; int auto.
  unfold OS_EVENT_TYPE_MUTEX; auto with zarith. 
  change (Byte.max_unsigned) with 255. auto with zarith.
  unfold OS_EVENT_TYPE_MUTEX; auto with zarith.  }
  intros. unfold OS_ERR_EVENT_TYPE; int auto.
 unfold OS_EVENT_TYPE_MUTEX; auto with zarith.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct (Int.eq i1 ($ OS_EVENT_TYPE_MUTEX)) eqn:eq1.
  2: { simpl in H15. change (Int.notbool Int.zero) with Int.one in H15.
          destruct H15; tryfalse. }
  eapply inteqeq in eq1.
  subst i1.

  destruct v'32;
  [ simpl AEventData | simpl AEventData | simpl AEventData | idtac |  simpl AEventData];
  hoare unfold.
  hoare_assert_pure (DMutex v v0 = DMutex (Vint32 i2) x0).
  {
    get_hsat Hsat.
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
  assert (Hget': get els (v'39,Int.zero) = Some (absmutexsem (x3 >>ᵢ $ 8) o, w)).
  {
    eapply EcbMod.join_get_r; eauto.
    eapply EcbMod.join_sig_get; eauto.
  }
  (* assign pip *)
  hoare forward.
  go.
  pure_auto.
  lets Hpip_eq: mutexpost_intlemma1 H42.
  rewrite Hpip_eq.
    rename H42 into Hpip_range.
  assert (Hpip_range': Int.unsigned (x3 >>ᵢ $ 8) <= Byte.max_unsigned).
  {
    clear -Hpip_range.
    change Byte.max_unsigned with 255.
  auto with zarith.
  }
  (* assign prio *)
  hoare forward.
  go.
  lets Hprio_range: postintlemma3 x3.
  lets Hprio_eq: mutpost_intlemma1 Hprio_range.
  change 255 with Byte.max_unsigned in Hprio_range.
  rewrite Hprio_eq.

  unfold AOSTCBList.
  hoare unfold.
  lets Hget_t: Mbox_common.TCBListP_head_in_tcb H44.
  destruct Hget_t as (st & sus & Hget_t).
  eapply TcbMod.join_get_r in Hget_t; eauto.
  assert (How: ((o = None) \/
                               (exists ot op, o = Some (ot, op) 
                                     /\ (exists prio m, get v'11 ot = Some (prio, rdy,m,false)
                                                                 /\ (prio = op
                                                                          \/ (prio = (x3 >>ᵢ $ 8) /\ (get v'16 op = Some Null \/get v'16 op = Some Holder)
                                                                                 /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) )))))
                 \/ ~((o = None) \/
                               (exists ot op, o = Some (ot, op) 
                                     /\ (exists prio m, get v'11 ot = Some (prio, rdy,m,false)
                                                                 /\ (prio = op
                                                                          \/ (prio = (x3 >>ᵢ $ 8) /\ (get v'16 op = Some Null \/get v'16 op = Some Holder)
                                                                                 /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) ))))))
  by tauto.
  unfold AOSTCBPrioTbl.
  hoare_lifts_trms_pre (absecblsid, abstcblsid, absptlsid).
Require Import gjb_mutex_common.
  mytac_lift_absop.
  destruct How as [How | Habt].
  2: {
         eapply abscsq_rule.
         apply noabs_oslinv.
         eapply mutexpost_absimp_owner_hold_abt';eauto.
         can_change_aop_solver. eapply absinfer_eq.
        apply absabort_rule.
      }
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutexpost_absimp_owner_hold';eauto.
   can_change_aop_solver.
   eapply absinfer_eq.
   hoare unfold.
   destruct How as [Hnone | Hsome].

  (* case1: o = None *)
      (* destruct Hnone as (Ho & Hpip_neq). *) subst o.
      assert (Hpip_neq: prio_available (x3 >>ᵢ $ 8) v'11).
      {  destruct H as (_ & _ & _ & H & _).
          destruct H as (_ & _ & How & Howp).
          destruct Howp as (Hnone & Hsome & Hidm).
          eapply Hnone; eauto.
        }
       assert (Hopv: opv = V$ OS_ERR_NOT_MUTEX_OWNER
                                \/ opv <> V$ OS_ERR_NOT_MUTEX_OWNER) by tauto.
  hoare_lifts_trms_pre (absecblsid, abstcblsid, ostmid, curtid, absptlsid).
  mytac_lift_absop.
       destruct Hopv as [Hopv | Habt].
       2: {
              eapply abscsq_rule.
              apply noabs_oslinv.
              eapply mutexpost_absimp_no_owner_abt';eauto.
              can_change_aop_solver. eapply absinfer_eq.
              apply absabort_rule.
              }
 
       (* if OSTCBCur ′ → OSTCBPrio !=ₑ pip ′ &&ₑ OSTCBCur ′ → OSTCBPrio !=ₑ prio ′ *)
        assert (Hprio: x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE 
                        \/ x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE) by tauto.
        destruct Hprio as [Hprio | Hprio].
        eapply H47 in Hprio. destruct Hprio as (tid0 & Hx2 & Hfalse). tryfalse.
        rewrite Hprio.
        assert (Htp_range: 0 <= Int.unsigned i5 < 64).
        {
          lets Htcb_rl: TCBList_P_imp_RL H44.
          simpl RL_TCBblk_P_List in Htcb_rl.
          destruct Htcb_rl as (Htcb_rl1 & _).
          eapply tcbblk_prio_range; eauto. 
         }
        assert (Htp_neq1: Int.eq i5 (x3 >>ᵢ $ 8) = false).
        {
          clear -Hpip_neq Hget_t.
          unfold prio_available in Hpip_neq.
          eapply Hpip_neq in Hget_t.
          int auto.
  Optimize Proof.
  Optimize Heap.
        }
        assert (Htp_neq2: Int.eq i5 ($ OS_MUTEX_AVAILABLE) = false).
        {
          clear -Htp_range. unfold OS_MUTEX_AVAILABLE. int auto.
        }
        hoare forward.
         go.
         clear -Hpip_range'; pure_auto.
         pure_auto.
         pure_auto.
         go.
        clear -Hprio_range; pure_auto.
        pure_auto.
        pure_auto.
        rewrite Htp_neq1, Htp_neq2.
        hoare unfold.
        instantiate (1:= Afalse).
        2: {
                eapply hoare_disj_afalseP_l_pre.
                rewrite Htp_neq1, Htp_neq2.
                 hoare unfold.
                  simpl in H64.
                 change (Int.ltu Int.zero (Int.notbool Int.zero) 
                                  && Int.ltu Int.zero (Int.notbool Int.zero)) with true in H64.
                simpl in H64. destruct H64; tryfalse.
              }
        hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid).
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpost_absimp_no_owner_err'; eauto.
        can_change_aop_solver.
        eapply absinfer_eq.
        (* EXIT_CRITICAL *)
        hoare forward prim.
        sep cancel APthreadAttr.
  sep cancel CapabilityInv.
        sep cancel tcbdllflag.
        unfold AOSTCBList.
        unfold tcbdllseg.
        unfold V_OSTCBPrev,V_OSTCBNext.
        sep pauto; try eauto.
        sep cancel (dllseg v'3).
        simpl dllseg.
        unfold node.
        sep pauto.
        sep cancel dllseg.
(*         sep cancel 1%nat 1%nat. *)
         unfold EvtInv. sep pauto.
         unfold AOSTCBPrioTbl; sep pauto.
         sep cancel ASemEIBs. sep cancel AMuxEIBs. 
         sep cancel AMqEIBs.
        sep cancel Astruct.
         sep cancel AOSEventFreeList.
        sep cancel AOSQFreeList.
        sep cancel AOSQFreeBlk.
         eapply AECBList_fold; eauto.
         eapply lzh_evsllseg_compose; eauto.
         sep cancel (evsllseg v'10).
         sep cancel evsllseg.
         unfold AEventNode.
         unfold AOSEvent.
        unfold node, AOSEventTbl.
        sep pauto; try eauto.
        sep cancel Astruct.
        sep cancel Aarray.  eauto.
        sep cancel AOSPostEventTbl. sep cancel p_local. 
        sep cancel Aier.
        eauto.
        split; auto. go. 
        unfolds; simpl; auto. auto. auto. auto.
        split; auto. go. auto.
        pure_auto.
        (* RETURN OS_ERR_NOT_MUTEX_OWNER *)
        hoare forward.
(*   } *)
  (* case 2: o = Some (tid, op) *)
  destruct Hsome as (ot & op & Ho & (p' &(*  st' & *) m' & Hget_ot & Hp_case)).
  subst o.
   assert (Hprio: x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 <> $ OS_MUTEX_AVAILABLE 
                        \/ x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 = $ OS_MUTEX_AVAILABLE) by tauto.
   destruct Hprio as [Hprio | Hprio].
   2 :{  eapply H46 in Hprio. destruct Hprio as (Hfalse & Hx2). tryfalse. }
   lets Ho_eq: H47 Hprio.
   destruct Ho_eq as (otid & Hx2 & Ho_eq).
   subst x0. inverts Ho_eq.
   assert (Heq1: Some (otid, x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) 
                                = Some (otid, x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) by auto.
   lets Hprio_range': H40 otid (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) Heq1.
  destruct Hprio_range' as (Hlt_pip & Hprio_range').

  (* if OSTCBCur ′ → OSTCBPrio !=ₑ pip ′ &&ₑ OSTCBCur ′ → OSTCBPrio !=ₑ prio ′ *)
  assert (Hp_case': (p' = x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8 /\ prio_available (x3 >>ᵢ $ 8) v'11) \/
          (p' = x3 >>ᵢ $ 8 /\(get v'16 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) =
          Some Null \/ get v'16 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = Some Holder)
          /\ (forall eid' p' ow wls', 
              EcbMod.get els eid' = Some (absmutexsem p' ow, wls') ->
              Int.ltu (x3 >>ᵢ $ 8) p' = true ->
              Int.eq p' (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false)) ).
  { destruct Hp_case as [Hp' | (Hp' & Hpr_neq & Hno_cre_mut)]; subst.
     left.
     destruct H as (_ & _ & _ & H & _).
     destruct H as (_ & _ & How & Howp).
     destruct Howp as (Hnone & Hsome & Hidm).
     split; auto.
      lets Hin: How Hget'.
      destruct Hin as (_ & Hin).
     eapply Hsome; eauto.
     clear -Hlt_pip.
     eapply semacc_int_eq_false.
     eapply ltu_eq_false. auto.
     right.
     splits; auto. eauto.
      introv Hce Hclt.
      assert (Hceq: Int.eq p' (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = false 
                              \/ Int.eq p' (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) = true)
      by (remember (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as cpr; clear -H; int auto).
      destruct Hceq as [Hceq | Hceq]; auto.
      false.
      eapply inteqeq in Hceq; subst.
      eapply Hno_cre_mut; eauto.
    }
  clear Hp_case. rename Hp_case' into Hp_case.
  hoare forward.
  go.
  clear -Hpip_range'; pure_auto.
  pure_auto.
  pure_auto.
  go.
  clear -Hprio_range; pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  hoare unfold;
  destruct (Int.eq i5 (x3 >>ᵢ $ 8)) eqn: eq1;
  destruct (Int.eq i5 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq2;
  simpl in H64;
  try rewrite int_ltu_zero_notbool_one_false in H64;
  try rewrite int_ltu_zero_notbool_zero_true in H64;
  simpl in H64; tryfalse.
  assert (Hot_neq: (v'38, Int.zero) <> otid).
  {
    assert (Ht: (v'38, Int.zero) <> otid \/ (v'38, Int.zero) = otid) by tauto.
    destruct Ht. auto. subst otid.
    unfold get in  Hget_ot. unfold TcbMap in Hget_ot.
    rewrite Hget_t in Hget_ot.
    inverts Hget_ot.
    destruct Hp_case as [(Hp' & _) | (Hp' & _ & _) ]; subst p';
    try rewrite Int.eq_true in eq1; try rewrite Int.eq_true in eq2; tryfalse.
  }
  assert (Hopv: opv = V$ OS_ERR_NOT_MUTEX_OWNER
                            \/ opv <> V$ OS_ERR_NOT_MUTEX_OWNER ) by tauto.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, curtid).
  destruct Hopv.
  2: {
              eapply abscsq_rule.
              apply noabs_oslinv.
              eapply mutexpost_absimp_not_owner_err_abt';eauto.
              can_change_aop_solver.
              clear -Hp_case; pure_auto. eapply absinfer_eq.
              apply absabort_rule.
              }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpost_absimp_not_owner_err';eauto.
  can_change_aop_solver.
  clear -Hp_case; pure_auto.
  eapply absinfer_eq.
  (*EXIT_CRITICAL*)
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold V_OSTCBPrev,V_OSTCBNext.
  sep pauto; try eauto.
  sep cancel (dllseg v'3).
  simpl dllseg.
  unfold node.
  sep pauto.
  sep cancel dllseg.
(*         sep cancel 1%nat 1%nat. *)
  unfold EvtInv.  sep pauto.
  unfold AOSTCBPrioTbl; sep pauto.
  trycancel_EvtInv.
  sep cancel Astruct.
  eapply AECBList_fold; eauto.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel (evsllseg v'10).
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node, AOSEventTbl.
  sep pauto; try eauto.
  sep cancel Astruct.
  sep cancel Aarray.  eauto.
  sep cancel AOSPostEventTbl. sep cancel p_local. 
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  split; auto. go.
  unfolds; simpl; auto. auto. auto. auto.
  split; auto. go. auto.
  pure_auto.
  (* RETURN OS_ERR_NOT_MUTEX_OWNER *)
  instantiate (1:= Afalse).
   hoare forward.
   eapply hoare_disj_afalseP_l_pre.
   hoare unfold.
    assert (Heqn: i5 = (x3 >>ᵢ $ 8) \/ i5 = (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)).
    {
      destruct (Int.eq i5 (x3 >>ᵢ $ 8)) eqn: eq1;
      destruct (Int.eq i5 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) eqn: eq2;
      simpl in H64;
      try rewrite int_ltu_zero_notbool_one_false in H64;
      try rewrite int_ltu_zero_notbool_zero_true in H64;
      simpl in H64; tryfalse;
      try eapply inteqeq in eq1;
      try eapply inteqeq in eq2;
      try subst i5; auto.
      destruct H64; tryfalse.
     }
   clear H64.
  unfold AOSTCBPrioTbl.
  hoare unfold.
  lets Hrptbl : H49.
  funfold H49.
   assert (Hot_eq: (v'38, Int.zero) = otid).
  {
    assert (Hot: (v'38, Int.zero) = otid \/ (v'38, Int.zero) <> otid) by tauto.
    destruct Hot as [Hot | Hot]. auto.
    lets Hop: H65 Hot Hget_t Hget_ot. 
    destruct H62 as (Hlh & Hhl). unfold RHL_PrioTbl_P in Hhl.
    destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & Hhl4). 
    clear -Hp_case Hlt_pip Heqn Hop Hget_t Hrptbl Hpip_range Hprio_range' Hhl2 Hhl3.
    destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
    destruct Heqn; subst i5; subst p'; tryfalse.
    eapply Hneq in Hget_t.
    rewrite Int.eq_true in Hget_t;
    tryfalse.
  unfold R_PrioTbl_P in Hrptbl. destruct Hrptbl as (Hhg & Hgh & dup).
  lets Htt: Hget_t.
    destruct Heqn; subst i5; subst p'; tryfalse.
  unfold TcbMod.get in Hget_t; unfold TcbMap in Hget_t;
  eapply Hgh in Hget_t; eauto.
  destruct Hneq as [Hnul | Hhold].
  eapply Hhl2 in Hnul. destruct Hnul as (Hr & Hn).
  destruct Hget_t as (Hnv & Hneq).
  rewrite Hnv in Hn; tryfalse.
  eapply Hhl3 in Hhold. destruct Hhold as (Hr & Hn).
  rewrite Hn in Hget_t. destruct Hget_t. inverts H. tryfalse.
   } 
  subst otid.
  unfold get in Hget_ot; unfold TcbMap in Hget_ot.
  rewrite Hget_t in Hget_ot.
  inverts Hget_ot.
  (* unfold OSRdyTbl*)
   unfold AOSRdyTblGrp.
   unfold AOSRdyTbl.
   unfold AOSRdyGrp.
  hoare unfold.
  rename H70 into Hlrtbl.
  (*get precise range of x,y,bitx,bity of OSCurTCB *)
  lets Htcb_p: H44.
  destruct Htcb_p as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs as (((op & ost) & om) & sus).
  destruct Htp as (Hvm & Hvp & Hrsl & Hrtsl).
  inverts Hveq.
  unfold V_OSTCBNext,V_OSTCBMsg,V_OSTCBPrio in Hnes,Hvm,Hvp.
  simpl in Hnes,Hvm,Hvp.
  inverts Hnes; inverts Hvm; inverts Hvp.
  lets Hget_ot: tcbjoin_get_a Htcj.
  eapply TcbMod.join_get_r in Hget_ot; eauto.
  rewrite Hget_t in Hget_ot. inverts Hget_ot.
  rename i4 into vx; rename i3 into vy.
  rename i2 into vbitx; rename i1 into vbity.
  assert (Hvyx_range: Int.unsigned vy < 8 /\ Int.unsigned vx < 8 /\ Int.unsigned vbitx <= 128).
  {
     clear -Hrsl. funfold Hrsl. mauto.
  }
  destruct Hvyx_range as (Hy_range & Hx_range & Hbx_range).
  assert (Hy_range': (Z.to_nat (Int.unsigned vy) < length v'8)%nat).
  {
    rewrite Hlrtbl.  clear -Hy_range.
    change (∘ OS_RDY_TBL_SIZE) with 8%nat.
    auto with zarith.
  }
  assert (Hy_range'_eq: Int.unsigned vy < Z.of_nat (length v'8)).
  { clear -Hy_range'. auto with zarith. }
  assert (Hy_range'':  Int.unsigned vy <= 7).
  { clear -Hy_range. int auto. }
  assert (exists i, nth_val' (Z.to_nat (Int.unsigned vy)) v'8 = Vint32 i /\
                    Int.unsigned i <= 255) as nth_val_rtbl.
  {
    lets Hx: array_int8u_nth_lt_len H66.
    eapply Hx.
    rewrite Hlrtbl.
    clear -Hy_range.
    change (∘ OS_RDY_TBL_SIZE) with 8%nat.
    auto with zarith.
  }
  destruct nth_val_rtbl as [rrow [nth_val_rtbl rrow_le_255]].
  lets Hup_eq: len_lt_update_get_eq Hy_range'_eq.
  instantiate (1:= (val_inj (and (Vint32 rrow) (Vint32 (Int.not vbitx))))) in Hup_eq.
  (* conditions about OSMapTbl ′ [OSTCBCur ′ → OSTCBY] *)
  unfold AOSMapTbl. 
  assert (Hmap_a: array_type_vallist_match Int8u OSMapVallist).
  { unfolds. unfold OSMapVallist. splits; auto; unfolds. }
  assert (Hmap_l: length OSMapVallist = 8%nat) by reflexivity.
  assert (Hprio_range_new: 0 <= Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7) < 8 
                                                /\ 0 <= Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3) < 8).
  { eapply int_usigned_tcb_range. split; eauto.
     remember (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) as prio.
     clear -H0; int auto. }
  destruct Hprio_range_new as (Hprio_range_and & Hprio_range_shl).
   assert (Hprio_range_shl':  (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) < 8)%nat).
   { clear -Hprio_range_shl. auto with zarith. }
    lets fff: nthval'_has_value Hmap_a Hmap_l Hprio_range_shl'.
    destruct fff as (vmy & Hvmy & Hvmy_true). eapply eq_sym in Hvmy_true.
    lets Hvmy_range: rule_type_val_match_int8u_elim Hvmy_true.
    destruct Hvmy_range as (vmy' & Heq & Hvmy_range).
    inverts Heq. rename vmy' into vmy.
    assert (Hprio_range_and':  (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)) < 8)%nat).
   { clear -Hprio_range_and. auto with zarith. }
    lets fff: nthval'_has_value Hmap_a Hmap_l Hprio_range_and'.
    destruct fff as (vmx & Hvmx & Hvmx_true). eapply eq_sym in Hvmx_true.
    lets Hvmx_range: rule_type_val_match_int8u_elim Hvmx_true.
    destruct Hvmx_range as (vmx' & Heq & Hvmx_range).
    inverts Heq. rename vmx' into vmx.
    assert (Hup_a: array_type_vallist_match Int8u 
                               (update_nth_val (Z.to_nat (Int.unsigned vy)) v'8 (Vint32 (rrow&ᵢInt.not vbitx)))).
    {
      eapply array_type_vallist_match_hold; eauto.
      simpl rule_type_val_match.
      lets Hand: not_and_p rrow_le_255 Hbx_range.
      clear -Hand; pure_auto.
    }
    lets Hup_nth: array_int8u_nth_lt_len Hup_a.
    rewrite update_nth_val_len_eq in Hup_nth. rewrite Hlrtbl in Hup_nth.
    change (∘ OS_RDY_TBL_SIZE) with 8%nat in Hup_nth.
    lets Hup_nth': Hup_nth Hprio_range_shl'. clear Hup_nth.
    destruct Hup_nth' as (vup & Hvup & Hvup_range).
  (* If (OSTCBCur ′ → OSTCBPrio ==ₑ pip ′) *)
  hoare forward.
  go.
  clear -Hpip_range'; pure_auto.
  pure_auto.
  hoare unfold.
  (*OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] &= ∼ OSTCBCur ′ → OSTCBBitX;ₛ*)
  hoare forward.
  struct_type_match_solver.
  rewrite nth_val_rtbl. rtmatch_solve.
  struct_type_match_solver.
  rewrite nth_val_rtbl. simpl. pauto.
  struct_type_match_solver.
  (* If (OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] ==ₑ ′ 0) *)
  hoare forward.
  struct_type_match_solver.
  rewrite update_nth_val_len_eq.
  clear -Hy_range'. auto with zarith.
  rewrite nth_val_rtbl. rewrite Hup_eq.
  rtmatch_solve.
  eapply le255_and_le255; eauto.
  rewrite nth_val_rtbl. rewrite Hup_eq.
  simpl; pure_auto.
  (* OSRdyGrp ′ &= ∼ OSTCBCur ′ → OSTCBBitY *)
  hoare unfold.
  hoare_assign.
  clear -H67. change Byte.max_unsigned with 255. pure_auto.
  struct_type_match_solver.

  (* pre-condition process *)
  rewrite nth_val_rtbl. rewrite Hup_eq.
  eapply backward_rule1.
  eapply adisj_mono;
  introv Hsat;
  ssplit_apure_in Hsat;
  sep_lift_context_in Hsat (Agvarmapsto OSRdyGrp);
  eapply astar_l_apure_intro in H73; eauto.
   eapply backward_rule1.
   eapply adisj_mono;
   eapply astar_assoc_intro; eauto.
   eapply backward_rule1.
   eapply disj_com_star.
  (* OSTCBCur ′ → OSTCBPrio =ₑ prio ′;ₛ *)
  hoare forward.
  clear -Hprio_range. pure_auto.
  (* OSTCBCur ′ → OSTCBY =ₑ prio ′ ≫ ′ 3;ₛ *)
  hoare forward.
   clear -Hprio_range. pure_auto.
  (* OSTCBCur ′ → OSTCBBitY =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBY];ₛ *)
  change (Int.ltu ($ 3) Int.iwordsize) with true.
  simpl val_inj in *.
  hoare forward.
  struct_type_match_solver.
  rewrite Hvmy. rewrite Hvmy_true. auto.
  rewrite Hvmy.
  (* OSTCBCur ′ → OSTCBX =ₑ prio ′ &ₑ ′ 7;ₛ *)
  hoare forward.
  clear -Hprio_range. pure_auto.
  (* OSTCBCur ′ → OSTCBBitX =ₑ OSMapTbl ′ [OSTCBCur ′ → OSTCBX];ₛ *)
  hoare forward.
  struct_type_match_solver.
  rewrite Hvmx. rewrite Hvmx_true. auto.
  rewrite Hvmx.
  (* OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ OSTCBCur ′ → OSTCBBitY;ₛ *)
  hoare remember (5 :: (* 1 :: 3 :: 4 :: *) nil)%nat pre.
  hoare forward.

    instantiate (1:= 
              ( [|val_inj
       (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
     val_inj
       (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) <> Vnull /\
     val_inj
       (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) <> Vundef|] **  
(*   [|Int.unsigned vbity <= 255|] ** *)
   GV OSRdyGrp @ char_t |-> Vint32 (Int.or (i5&ᵢInt.not vbity) vmy) \\//
    [|val_inj
       (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj
       (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vnull|] ** 
(*   [|Int.unsigned vbity <= 255|] ** *)
  GV OSRdyGrp @ char_t |-> Vint32 (Int.or i5 vmy)) **
  H73
      ). 

  eapply backward_rule1.
  eapply disj_split_star.
  hoare unfold.
  hoare forward.
  hoare forward.
  lets Hand: int_lemma1 H67 H61.
  clear -Hand. pure_auto.
  struct_type_match_solver.
  eapply disj_com_star.
  left. sep pauto. 
  hoare forward.
  clear -H67; pure_auto.
  struct_type_match_solver.
  eapply disj_com_star.
  right. sep pauto.
  hoare unfold.
  (* OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] =ₑ
      OSRdyTbl ′ [OSTCBCur ′ → OSTCBY] |ₑ OSTCBCur ′ → OSTCBBitX;ₛ*)
  hoare forward.
  struct_type_match_solver.
  rewrite update_nth_val_len_eq. rewrite Hlrtbl.
  clear -l0. change (Z.of_nat ∘ OS_RDY_TBL_SIZE) with 8. auto with zarith.
  rewrite Hvup. clear -Hvup_range. simpl. pure_auto.
  struct_type_match_solver.
  rewrite Hvup. pure_auto.
  struct_type_match_solver.
  clear -l0. change (Z.of_nat ∘ OS_RDY_TBL_SIZE) with 8. auto with zarith.
  rewrite update_nth_val_len_eq. rewrite Hlrtbl.
  clear -l0. change (Z.of_nat ∘ OS_RDY_TBL_SIZE) with 8. auto with zarith.
  (* OSTCBPrioTbl ′ [prio ′] =ₑ 〈 OS_TCB ∗ 〉 OSTCBCur ′ *)
  hoare forward.
  clear -Hprio_range. pure_auto.

  (* pre-condition process *)
  rewrite Hvup.
  simpl val_inj.
  eapply backward_rule1.
  eapply adisj_mono;
  introv Hsat;
  ssplit_apure_in Hsat;
  sep_lift_context_in Hsat (Agvarenv' OSPlaceHolder); (* use for assign PlaceHolder *)
  sep_lift_context_in Hsat (Agvarmapsto OSRdyGrp);
  sep_lift_context_in Hsat (Astruct (v'38, Int.zero));
  sep_lift_context_in Hsat (GAarray OSTCBPrioTbl);
  sep_lift_context_in Hsat (GAarray OSRdyTbl);
  eapply astar_l_apure_intro in H70; eauto.
   do 4 (eapply backward_rule1; try (eapply adisj_mono; eapply astar_assoc_intro; eauto)).
   eapply backward_rule1.
   eapply disj_com_star_gen.
    split; intros; sep auto.
   (* OSTCBPrioTbl ′ [pip ′] =ₑ 〈 OS_TCB ∗ 〉 PlaceHolder;ₛ *)
    unfold PlaceHolder.
    hoare remember (1 :: (* 2 :: 3 :: *) nil)%nat pre.
    hoare forward.
instantiate (1:=
      (((([|val_inj
          (if Int.eq op (x3 >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
        val_inj
          (if Int.eq op (x3 >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) <> Vnull /\
        val_inj
          (if Int.eq op (x3 >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) <> Vundef|] **
      GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
        (update_nth_val
           (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
           (update_nth_val (Z.to_nat (Int.unsigned vy)) v'8
              (Vint32 (rrow&ᵢInt.not vbitx))) (Vint32 (Int.or vup vmx)))) **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned (x3 >>ᵢ $ 8)))  (* update to palceholder *)
                                  (update_nth_val (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2
                                                                (Vptr (v'38, Int.zero)))
                                  (Vptr vhold_addr)) ) **
    Astruct (v'38, Int.zero) OS_TCB_flag
      (vv
       :: v'13
          :: x15
             :: om
                :: Vint32 i7
                   :: Vint32 i6
                      :: Vint32 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                         :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                            :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                               :: Vint32 vmx :: Vint32 vmy :: nil)) **
   ([|val_inj
        (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
      val_inj
        (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)) <> Vnull /\
      val_inj
        (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)) <> Vundef|] **
    GV OSRdyGrp @ char_t |-> Vint32 (Int.or (i5&ᵢInt.not vbity) vmy) \\//
    [|val_inj
        (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
      val_inj
        (if Int.eq (rrow&ᵢInt.not vbitx) ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)) = Vnull|] **
    GV OSRdyGrp @ char_t |-> Vint32 (Int.or i5 vmy)) \\//
   ((([|val_inj
          (if Int.eq op (x3 >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
        val_inj
          (if Int.eq op (x3 >>ᵢ $ 8)
           then Some (Vint32 Int.one)
           else Some (Vint32 Int.zero)) = Vnull|] **
      GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) v'8) **
     GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) 
                     (update_nth_val (Z.to_nat (Int.unsigned (x3 >>ᵢ $ 8))) v'2 (Vptr vhold_addr))) ** (* update to palceholder *)
    Astruct (v'38, Int.zero) OS_TCB_flag
      (vv
       :: v'13
          :: x15
             :: om
                :: Vint32 i7
                   :: Vint32 i6
                      :: Vint32 op
                         :: Vint32 vx
                            :: Vint32 vy :: Vint32 vbitx :: Vint32 vbity :: nil)) **
   GV OSRdyGrp @ char_t |-> Vint32 i5) ** H70
      ).

  hoare normal pre.
  hoare normal post.
  eapply backward_rule1.
  eapply disj_split_star.
  (* eapply forward_rule1.
  eapply disj_com_star. *)
  hoare unfold.
  hoare forward.
  (* case 1 *)
  hoare unfold.
  mytac_lift_absop.
  eapply forward_rule2.
  eapply assign_rule_array_g_aop.
  intro.
  split.
  intro.
  sep cancel A_dom_lenv.
  sep cancel (GAarray OSTCBPrioTbl). eauto.
  intro.
  sep pauto.
  simpl; auto.
  2 : symbolic execution.
  intros.
  sep normal; sep eexists.
  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel Agvarenv'.
  eauto.

  sep_lift_context_in H77 A_dom_lenv.
  apply astar_l_adomlenv_elim in H77.
  destruct H77.
  clear -H77.
  unfolds in H77.
  unfolds. unfold EnvMod.indom. introv Hget.
  destruct Hget as ((l & t) & Hget).
  assert (Hnot: ~ (ListSet.set_In (OSPlaceHolder, t)
        ((pevent, OS_EVENT ∗) :: (pip, char_t) :: (prio, char_t) :: nil))).
  unfolds. simpl. intros. repeat (destruct H; tryfalse).
  eapply Hnot.
  erewrite H77.
  eauto.

  simpl; auto.
  clear -Hpip_range'; pure_auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  clear -Hlt_pip Hprio_range'. rewrite Intlt_true_is_Zlt in Hlt_pip.  auto with zarith.
  eapply eq_vptr; eauto.
  rewrite update_nth_val_len_eq. rewrite H63.
  clear -Hlt_pip Hprio_range'. rewrite Intlt_true_is_Zlt in Hlt_pip.  auto with zarith.

  intros.
  sep eexists. 
  sep cancel p_local.
  simpl; auto.

  intros.
  eapply disj_com_star.
  left. sep pauto.
  (* case 2 *)
  hoare unfold.
  mytac_lift_absop.
  eapply forward_rule2.
  eapply assign_rule_array_g_aop.
  intro.
  split.
  intro.
  sep cancel A_dom_lenv.
  sep cancel (GAarray OSTCBPrioTbl). eauto.
  intro.
  sep pauto.
  simpl; auto.
  2 : symbolic execution.
  intros.
  sep normal; sep eexists.
  eapply cast_rv_tptr.
  eapply addrof_gvar_rv.
  apply  astar_l_anotinlenv_intro.
  sep cancel Agvarenv'.
  eauto.

  sep_lift_context_in H75 A_dom_lenv.
  apply astar_l_adomlenv_elim in H75.
  destruct H75.
  clear -H75.
  unfolds in H75.
  unfolds. unfold EnvMod.indom. introv Hget.
  destruct Hget as ((l & t) & Hget).
  assert (Hnot: ~ (ListSet.set_In (OSPlaceHolder, t)
        ((pevent, OS_EVENT ∗) :: (pip, char_t) :: (prio, char_t) :: nil))).
  unfolds. simpl. intros. repeat (destruct H; tryfalse).
  eapply Hnot.
  erewrite H75.
  eauto.

  simpl; auto.
  clear -Hpip_range'; pure_auto.
  auto.
  clear -Hlt_pip Hprio_range'. rewrite Intlt_true_is_Zlt in Hlt_pip.  auto with zarith.
  eapply eq_vptr; eauto.
  rewrite H63.
  clear -Hlt_pip Hprio_range'. rewrite Intlt_true_is_Zlt in Hlt_pip.  auto with zarith.

  intros.
  sep eexists. 
  sep cancel p_local.
  simpl; auto.

  intros.
  eapply disj_com_star.
  right. sep pauto.
  (* end of assign PlaceHolder *)
  lets Hrtsl': Hrtsl.
  destruct Hrtsl' as (_ & Hrtsl' & _ & _).
  assert (Heqs: (op, rdy, om, false) = (op, rdy, om, false)) by auto.
  eapply Hrtsl' in Heqs.
  unfold RdyTCBblk, V_OSTCBStat, V_OSTCBDly,V_OSTCBPrio in Heqs.
  simpl in Heqs.
  destruct Heqs as ((_ & Hpip_rtbl) & Hsts & Hdly).
  inverts Hsts. inverts Hdly. clear Hrtsl'.
  assert (Hpip_neq_pr: x3 >>ᵢ $ 8 <> x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8).
  {  clear -Hlt_pip. 
      eapply semacc_int_eq_false;
      rewrite Int.eq_sym;
      eapply ltu_eq_false; eauto.
    }
  (* If (pevent ′ → OSEventGrp !=ₑ ′ 0) *)
  hoare unfold.
  hoare forward.
  struct_type_match_solver.
  pure_auto.
  pure_auto.

  (* iffalse: wait list = nil  *)
   2:{
   instantiate (1:= Afalse).
    eapply hoare_disj_afalseP_l_pre.
    hoare unfold.
   destruct (Int.eq i0 ($ 0)) eqn: eq1;
   simpl in H70.
  2 : { destruct H70; tryfalse. }
  clear H70. eapply inteqeq in eq1. subst i0.
  (* pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ ′ OS_MUTEX_AVAILABLE;ₛ *)
  hoare forward.
  struct_type_match_solver.
  (* pevent ′ → OSEventPtr =ₑ NULL;ₛ *)
  hoare forward.
  (* start get absdata *)
  assert (Hw: w = nil).
  {
    destruct v'18.
    (* v'31 = nil *)
    assert (v'10 = Vptr (v'39, Int.zero)).
    { destruct H10. subst v'10; tryfalse. destruct H10. subst v'10.
      clear -H26. destruct x0.
      simpl in H26. 
      destruct (beq_pos v'39 b && Int.eq Int.zero i0) eqn: eq1.
    2 :{ destruct x7; tryfalse. }  
      destruct (beq_pos v'39 b) eqn: eq2;
      destruct (Int.eq Int.zero i0) eqn:eq3; 
      simpl in eq1; tryfalse.
      rewrite beq_pos_Pos_eqb_eq in eq2.
      apply Pos.eqb_eq in eq2.
      apply inteqeq in eq3.
      subst; auto.
      } 
     subst v'10. 
    eapply ecblist_ecbmod_get_mutex in H13; eauto.
    destruct H13 as (ms & xx & Hnil & _).
    unfold get in Hget'. unfold EcbMap in Hget'.
    rewrite Hget' in Hnil. inverts Hnil. auto.
    (* v'31 <> nil *)
     eapply ecblist_ecbmod_get_mutex' in H13; eauto.
     2 : { apply eq_sym. eapply get_ectr_sing; eauto. }
     destruct H13 as (ms & xx & Hnil & _).
     unfold get in Hget'. unfold EcbMap in Hget'.
    rewrite Hget' in Hnil. inverts Hnil. auto.
  }
  subst w.

  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat (GAarray OSTCBPrioTbl).
  eapply disj_split_star in Hsat; eauto.
  hoare unfold.
  hoare forward.

  (* case1: OSTCBCur->OSTCBPrio = pip /\ pevent->OSEventGrp = 0 *)
  hoare unfold.
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq1.
  simpl in H70; tryfalse;
  eapply inteqeq in eq1.
  subst op.
  assert (Hopv: opv = V$ OS_NO_ERR \/ opv <> V$ OS_NO_ERR) by tauto.
  hoare_lifts_trms_pre (absecblsid, abstcblsid, ostmid, curtid, absptlsid).
  mytac_lift_absop.
  destruct Hopv as [Hopv | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpost_absimp_nowt_return_prio_succ_abt';eauto.
        can_change_aop_solver.
        unfold can_change_aop. fold can_change_aop.
        splits; try splits; try auto; can_change_aop_solver. eapply absinfer_eq.
        apply absabort_rule.
      }
     eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexpost_absimp_nowt_return_prio_succ';eauto.
    can_change_aop_solver.
    unfold can_change_aop. fold can_change_aop.
    splits; try splits; try auto; can_change_aop_solver. eapply absinfer_eq.
    subst opv.
    assert (Hprio_ptbl_true: rule_type_val_match OS_TCB ∗ 
                                       (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = true).
   { eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
      rewrite H63. clear -Hprio_range'. auto with zarith. }
   lets Hptbl_prio: rule_type_val_match_ptr_elim Hprio_ptbl_true.
    assert (nth_val_ptbl:  (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = Vnull 
                                          \/ (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = Vptr vhold_addr).
    {
        destruct Hptbl_prio as [Hnull | (pid & Hpid)]. auto.
        right.
        rewrite Hpid.
        assert (Hp: pid = vhold_addr \/ pid <> vhold_addr) by tauto.
        destruct Hp as [Hp | Hp]. subst pid; auto.
        eapply H49 in Hp; eauto.
        instantiate (1:= (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) in Hp.
        2 : { remember ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) as prio. clear -Hprio_range'. int auto. }
        2 : { unfold nat_of_Z. eapply nth_val'_imp_nth_val_vptr; eauto. }
        destruct Hp as (Hpst & Hpm & Hp).
        lets Hprio_neq_pip: ltu_eq_false Hlt_pip.
        destruct Hp_case as [(Hp_eq & Hpra) | (Hp_eq & Hnuv & Hpra)].
        rewrite Hp_eq in Hprio_neq_pip. rewrite Int.eq_true in Hprio_neq_pip. tryfalse.
        unfold RH_PrioTbl_P in H62. destruct H62 as (Hlh & Hhl).
        destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & Hhl4 (* & Hhl5 *)).
        destruct Hnuv as [Hnul | Hhold].
        eapply Hhl2 in Hnul. destruct Hnul as (Hr & Hn).
        clear -Hn Hpid. 
        change (nth_val
       ∘ (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))
       v'2) with (nth_val
         (Z.to_nat
            (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
         v'2) in Hn.
        eapply nth_val'_imp_nth_val_vptr in Hpid. rewrite Hn in Hpid.
        inverts Hpid.
        eapply Hhl3 in Hhold. destruct Hhold as (Hr & Hn). 
        clear -Hn Hpid. 
        change (nth_val
       ∘ (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))
       v'2) with (nth_val
         (Z.to_nat
            (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))
         v'2) in Hn.
        eapply nth_val'_imp_nth_val_vptr in Hpid. rewrite Hn in Hpid.
        inverts Hpid. auto.
    }
    lets Hpip_range_shl: shru_3_lt_8 Hpip_range.
    lets Hpip_range_and: post_intlemma4 Hpip_range.
    assert (Hvy_eq: ((x3 >>ᵢ $ 8) >>ᵢ $ 3) = vy).
    { clear -Hrsl. funfold Hrsl. auto. }
    assert (Hvby_eq: $ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3) = vbity).
    { clear -Hrsl. funfold Hrsl. auto. }
   assert (Hvx_eq: ((x3 >>ᵢ $ 8)&ᵢ$ 7) = vx).
    { clear -Hrsl. funfold Hrsl. auto. }
    assert (Hvbx_eq: $ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7) = vbitx).
    { clear -Hrsl. funfold Hrsl. auto. }
    assert (Hvbx_eq': rrow&ᵢvbitx = vbitx).
    {
      subst vbitx. subst vy.
      eapply Hpip_rtbl; eauto.
      unfold nat_of_Z.
      eapply nth_val'_imply_nth_val; eauto.
     }
    destruct Hp_case as [(Hpeq & _) | (_ & Hp_case & Hpr_no_use)].
    clear -Hpeq Hlt_pip.
    rewrite Hpeq in Hlt_pip.
    eapply ltu_eq_false in Hlt_pip.
    rewrite Int.eq_true in Hlt_pip.
    tryfalse.
    lets Hdup_eq: double_update_simpl Hy_range'.
     assert (Hdup_eq_and: (and (Vint32 (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))))
                                                     (Vint32 (Int.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))))) 
                                         = (and (Vint32 rrow) (Vint32 (Int.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))))).
      { simpl. rewrite Int.and_assoc. rewrite Int.and_idem. auto. }
   (* EXIT_CRITICAL *)
    hoare forward prim.
    unfold AOSMapTbl.
    sep cancel (GAarray OSMapTbl).
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel (Agvarenv' OSPlaceHolder).
    sep cancel (Aptrmapsto vhold_addr).
    sep cancel Aier.
    sep cancel p_local.
    unfold EvtInv.
    3 : {  destruct nth_val_ptbl as [nth_vnull | nth_vhold];
             [ eapply return_r_pt_p''  | eapply return_r_pt_p]; eauto;
            try (eapply nth_val'_imply_nth_val; eauto);
            rewrite H63; clear -Hprio_range'; auto with zarith.
           }
    3: {
            eapply return_rl_rt_pt_p; auto.
            eapply H64 in Hget_t. clear -Hget_t. destruct Hget_t. auto.
            eauto.
            rewrite update_nth_val_len_eq. rewrite Hlrtbl. auto.
            eauto. auto.
            instantiate (1:= (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7)))).
            eapply int_lemma1; eauto.
            eapply len_lt_update_get_eq; eauto.
            erewrite Hdup_eq. rewrite Hdup_eq_and.
            simpl. eauto.
            eauto.
            eapply OSTimeDlyPure.rtbl_remove_RL_RTbl_PrioTbl_P_hold; eauto.
            remember ((x3 >>ᵢ $ 8)) as pip.  clear -Hpip_range. int auto.
            unfold nat_of_Z. eapply nth_val'_imply_nth_val; eauto.
            eauto.
          }
    3: { split.
           eapply array_type_vallist_match_hold; try rewrite update_nth_val_len_eq ; eauto.
           eapply array_type_vallist_match_hold; eauto.
           rewrite H63. clear -Hprio_range'. auto with zarith.
           rewrite H63. clear -Hpip_range. auto with zarith.
           do 2 rewrite update_nth_val_len_eq. auto.
        }
   3: { eapply return_rh_ctcb; eauto. }
   3: { eapply mutex_rh_tcblist_ecblist_p_hold; eauto.
          rewrite TcbMod.map_get_set; eauto.
          eapply RH_TCBList_ECBList_P_post_changeprio'; eauto.
       }
      unfold AECBList.
      sep pauto.
      eapply lzh_evsllseg_compose.
      sep cancel (evsllseg v'10).
      sep cancel evsllseg. 
      sep cancel APthreadAttr.
  sep cancel CapabilityInv.
      unfold AEventNode.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep normal. do 3 eexists. exists (Vint32 i).
      sep eexists.
      sep split; try sep cancel Aarray; eauto.
      instantiate (29:= v'39).
      sep cancel (Astruct (v'39, Int.zero)).
      instantiate (26 := (DMutex (Vint32 (Int.or x3 ($ OS_MUTEX_AVAILABLE))) Vnull)).
      simpl AEventData.
      sep pauto.
      sep cancel AOSEventFreeList.
      sep cancel AOSQFreeList.
      sep cancel AOSQFreeBlk.
    2 : { unfold V_OSPostEventGrp; simpl; eauto. }
    2:{ unfold V_OSEventGrp; auto. }
    2: { splits; auto. 
           lets Hor_range: int_auxxx H24.
           struct_type_match_solver.  }
    2: { unfold V_OSEventListPtr; simpl; eauto. }
    2 : { eauto. } 
    2 : { eauto. } 
    5: { eapply ecblistp_hold; eauto.
           split; auto. 
           destruct v'18.
            left. split; auto.
     destruct H10. subst v'10; tryfalse. destruct H10. subst v'10.
      clear -H26. destruct x0.
      simpl in H26. 
      destruct (beq_pos v'39 b && Int.eq Int.zero i0) eqn: eq1.
    2 :{ destruct x7; tryfalse. }  
      destruct (beq_pos v'39 b) eqn: eq2;
      destruct (Int.eq Int.zero i0) eqn:eq3; 
      simpl in eq1; tryfalse.
      rewrite beq_pos_Pos_eqb_eq in eq2.
      apply Pos.eqb_eq in eq2.
      apply inteqeq in eq3.
      subst; auto. 
      right.
      eapply get_ectr_sing; eauto.
            (* end of 2 case *)
            (* ECBList_P rdy *)
      eapply ecblist_p_mutexpend_changeprio; eauto.
            (*R_ECB_ETbl_P *)
      eapply return_r_ecb_et_p'; eauto.
        }
      erewrite Hdup_eq. rewrite Hdup_eq_and. 
      unfold AOSTCBList.
      unfold tcbdllseg.
      sep pauto.
      sep cancel (dllseg v'3).
      simpl dllseg.
      unfold node.
      sep pauto.
      sep cancel dllseg.
      sep cancel Astruct.
(*       sep cancel (Astruct (v'37, Int.zero)). *)
      2: { unfold V_OSTCBPrev; simpl; auto. }
      2: { unfold V_OSTCBNext; simpl; auto. }
      2: { split; auto. struct_type_match_solver. }
      2: { eapply return_tcbl_p_alt; eauto. }
      3: { eapply TcbMod.joinsig_set_set; eauto. }
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
       instantiate (2:= if Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))) ($ 0)
                                  then Vint32 (Int.or (i5&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))) vmy)
                                  else Vint32 (Int.or i5 vmy)). 
     3: { assert (Hrange: Int.unsigned (Int.or (i5&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))) vmy) <= 255).
            { eapply int_unsigned_or_prop'; eauto. eapply int_lemma1; eauto. }
            assert (Hrange': Int.unsigned (Int.or i5 vmy) <= 255).
            { eapply int_unsigned_or_prop'; eauto. }
            destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))) ($ 0)) eqn: eq1;
            simpl; clear -Hrange Hrange'; pure_auto.
          }
     3: { split.
            eapply array_type_vallist_match_hold;try rewrite update_nth_val_len_eq ; eauto.
            rewrite Hlrtbl. change (∘ OS_RDY_TBL_SIZE) with 8%nat. auto.
            simpl.
            assert (Hrange: Int.unsigned (Int.or vup vmx) <= 255) 
                        by (eapply int_unsigned_or_prop'; eauto).
            clear -Hrange; pure_auto.
           do 2 rewrite update_nth_val_len_eq. auto.
        }

      (**)
      2 : { destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))) ($ 0)) eqn: eq1.
             eapply return_rl_t_g_p;  eauto.
              simpl. erewrite eq1. clear -H ; pure_auto.
              eauto.
              eapply return_rl_t_g_p'; eauto. 
              simpl.  erewrite eq1. simpl; auto. eauto. }

        sep_lift_context tcbdllflag.
        sep_lift_context_in H77 tcbdllflag.
        eapply tcbdllflag_hold; try sep cancel tcbdllflag.
        eapply tcbdllflag_hold_middle.
        simpl. unfold V_OSTCBflag, V_OSTCBNext.
        simpl. auto.
        unfold AEventData in H77.
        eapply disj_split_star in H77.
        destruct H77;  ssplit_apure_in H77;
        destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))) ($ 0)) eqn: eq1;
        try (simpl in H78; destruct H78; tryfalse);
        sep cancel (Agvarmapsto OSRdyGrp); eauto.
        Require Import gjb_common.
        3:{ eapply return_tcbl_p''; eauto. }
       sep_lift_context_in H77 tcbllsegevaux.
       sep_lift_context tcbllsegevaux.
        eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
        sep cancel tcbllsegevaux.
        2:{  eapply tcb_linked_list_same_next_split.
                eapply tcb_linked_list_same_next_self; eauto.
                rewrite <- nil_simp.
                change ((vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7) with (nil ++ (vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7).
                eapply tcb_linked_list_same_next_mid; eauto. }
  sep_lift_context_in H77 ASemEIBs. 
  instantiate (7:= v'27).
  instantiate (6:= v19).
  lets Hsat': ASemEIBs_set_none_preserve Hget' H77.
  eapply ASemEIBs_set_none_preserve in H77; eauto. 
  sep_lift_context_in H77 AMuxEIBs. 
  instantiate (5:= v'28).
  instantiate (4:= v20).
  lets Hs: AMuxEIBs_set_none_preserve Hget' H77.
  eapply AMuxEIBs_set_none_preserve in H77; eauto.
  sep_lift_context_in H77 AMqEIBs. 
  instantiate (3:= v'29).
  instantiate (2:= v21).
  lets Hss: AMqEIBs_set_none_preserve Hget' H77.
  eapply AMqEIBs_set_none_preserve in H77; eauto.
  trycancel_EvtInv.
  cancel_corecommuinv.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)
  
       sep_lift_context_in H77 tcbllsegevaux.
       sep_lift_context tcbllsegevaux.
        eapply tcbllsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
        sep cancel tcbllsegevaux.
        2:{  eapply tcb_linked_list_same_next_split.
                eapply tcb_linked_list_same_next_self; eauto.
                rewrite <- nil_simp.
                change ((vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7) with (nil ++ (vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7).
                eapply tcb_linked_list_same_next_mid; eauto. }
  sep_lift_context_in H77 ASemEIBs.
  lets Hsat': ASemEIBs_set_none_preserve Hget' H77.
  eapply ASemEIBs_set_none_preserve in H77; eauto. 
  sep_lift_context_in H77 AMuxEIBs. 
  lets Hs: AMuxEIBs_set_none_preserve Hget' H77.
  eapply AMuxEIBs_set_none_preserve in H77; eauto.
  sep_lift_context_in H77 AMqEIBs.
  lets Hss: AMqEIBs_set_none_preserve Hget' H77.
  eapply AMqEIBs_set_none_preserve in H77; eauto.
  trycancel_EvtInv.
  cancel_corecommuinv. 
  cancel_partitioninv.
  eauto.
  eapply mq_ecb_p_mux_set_preserve; eauto. 
  eapply mux_ecb_p_mux_set_preserve; eauto.
  eapply sem_ecb_p_mutex_set_preserve; eauto.
  eapply RH_PrioTbl_P_update_vhold; eauto.
  clear -Hpip_range. split; auto.
  apply Int.unsigned_range_2.
  eapply RH_PrioTbl_P_update_tcb; eauto.   
  clear -Hprio_range'. unfold OS_MUTEX_KEEP_LOWER_8.  splits; eauto; int auto. 
  eapply Z_land_range_lo_r; int auto. eapply Z_land_range; int auto. 
  unfold OS_MUTEX_KEEP_LOWER_8. auto with zarith.
  eapply Z_land_range; eapply Int.unsigned_range_2.
  auto. eapply H64 in Hget_t. destruct Hget_t; auto.

  pure_auto.
       (* end of EXIT_CRITICAL *)
  hoare forward.
  introv Hs. simpl in Hs; inverts Hs.
  splits; eauto.
  change (Int.unsigned ($ OS_NO_ERR)) with 0.
  auto with zarith.
  simpl in H70; tryfalse.
     (* case2 : OSTCBCur->OSTCBPrio <> pip /\ pevent->OSEventGrp = 0 *)
  hoare unfold.
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  simpl in H70;  tryfalse.
  destruct H70; simpl in H70; tryfalse.
  destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
  
    assert (Hopv: opv = V$ OS_NO_ERR \/ opv <> V$ OS_NO_ERR) by tauto.
  hoare_lifts_trms_pre (absecblsid, abstcblsid, ostmid, curtid, absptlsid).
  mytac_lift_absop.
  destruct Hopv as [Hopv | Habt].
  2: {
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply mutexpost_absimp_nowt_no_return_prio_succ_abt';eauto.
        can_change_aop_solver. eapply absinfer_eq.
        apply absabort_rule.
      }
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexpost_absimp_nowt_no_return_prio_succ';eauto.
    can_change_aop_solver. eapply absinfer_eq.
    subst opv.
    (* EXIT_CRITICAL *)
    hoare forward prim.
    unfold AOSMapTbl.
    unfold AOSRdyTblGrp.
    unfold AOSRdyTbl.
    unfold AOSRdyGrp.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    unfold EvtInv in *.
    unfold AECBList.
    unfold AMuxEIBs in *.
    unfold tcbdllseg.
    sep pauto; eauto.
    sep cancel (dllseg v'3).
    simpl dllseg.
    unfold node.
    sep pauto.
    sep cancel dllseg.
    sep cancel Astruct.
    sep cancel AOSEventFreeList.
    sep cancel AOSQFreeList.
    sep cancel AOSQFreeBlk.
    sep cancel APthreadMutex.
    sep cancel AMuxCap.

    eapply lzh_evsllseg_compose.
    sep cancel (evsllseg v'10).
    sep cancel evsllseg.
    unfold AEventNode.
    unfold AOSEvent.
    unfold node.
    unfold AOSEventTbl. sep normal. do 3 eexists. exists (Vint32 i).
    sep pauto; try sep cancel Aarray; eauto.
    sep cancel Astruct.
    sep cancel APthreadAttr.
    sep cancel CapabilityInv.
    sep cancel p_local. sep cancel Aier.
    instantiate (6 := (DMutex (Vint32 (Int.or x3 ($ OS_MUTEX_AVAILABLE))) Vnull)).
    unfold AEventData in *.
    unfold V_OSEventType,V_OSEventCnt,V_OSEventPtr.
    sep pauto.
    sep_lift_context_in H75 ASemEIBs.
    eapply ASemEIBs_set_none_preserve in H75; eauto. 
    sep_lift_context_in H75 AMqEIBs.
    eapply AMqEIBs_set_none_preserve in H75; eauto.
    sep cancel AMqEIBs. sep cancel ASemEIBs. eauto.
    cancel_corecommuinv.
    cancel_partitioninv.
    eauto.
    unfold V_OSPostEventGrp; simpl; eauto.
    unfold V_OSEventGrp; simpl; auto.
    splits; auto.
    lets Hor_range: int_auxxx H24.
    struct_type_match_solver.
    unfold V_OSEventListPtr; simpl; auto.
    eauto. eauto.
    unfold V_OSTCBNext; simpl; auto.
    splits; auto. struct_type_match_solver. go.
    clear -H67; pure_auto.
(*     eapply RH_ECBlk_EIBlk_Mux_P_remove_owner; eauto. *)
    2:{ eapply R_PrioTbl_P_update_vhold'; eauto. }
    2:{ eapply RL_RTbl_PrioTbl_P_update_vhold'; eauto. }
    2:{ split.
    eapply array_type_vallist_match_hold; try rewrite update_nth_val_len_eq ; eauto.
    rewrite H63. clear -Hpip_range. auto with zarith.
    rewrite update_nth_val_len_eq ; eauto. }
    eapply RH_PrioTbl_P_update_vhold; eauto.
    clear -Hpip_range. split; auto. apply Int.unsigned_range_2.
    eapply mq_ecb_p_mux_set_preserve; eauto.
    eapply mux_ecb_p_mux_set_preserve; eauto.
    eapply sem_ecb_p_mutex_set_preserve; eauto.


    (*ECBList_P *)
    eapply ecblistp_hold; eauto.
    split; auto.
    destruct v'18.
    left. split; auto.
    destruct H10. subst v'10; tryfalse. destruct H10. subst v'10.
    clear -H26. destruct x5.
    simpl in H26. 
    destruct (beq_pos v'39 b && Int.eq Int.zero i0) eqn: eq1.
    2 :{ destruct x7; tryfalse. }  
    destruct (beq_pos v'39 b) eqn: eq2;
    destruct (Int.eq Int.zero i0) eqn:eq3; 
    simpl in eq1; tryfalse.
    rewrite beq_pos_Pos_eqb_eq in eq2.
    apply Pos.eqb_eq in eq2.
    apply inteqeq in eq3.
    subst; auto. 
    right.
    eapply get_ectr_sing; eauto.

    eapply RH_ECBlk_EIBlk_Mux_P_remove_owner; eauto. 
     (* end of 2 case *)
     (* end of ECBList_P *)
     eapply mutex_rh_tcblist_ecblist_p_hold; eauto.

     pure_auto.
     (* end of EXIT_CRITICAL *)
      hoare forward.
      introv Hs. simpl in Hs; inverts Hs; auto.
      splits; eauto.
      change (Int.unsigned ($ OS_NO_ERR)) with 0.
      auto with zarith.

  hoare unfold. rewrite Int.eq_true in eq2; tryfalse. }

  (* iftrue: exists wait list *)
  hoare unfold.
  destruct (Int.eq i0 ($ 0)) eqn: eq1;
  simpl in H70; try  change (Int.notbool Int.one) with Int.zero in H70; tryfalse.
  clear H58 H75 H76.
  assert (Hvy_eq: (op >>ᵢ $ 3) = vy).
    { clear -Hrsl. funfold Hrsl. auto. }
    assert (Hvby_eq: $ 1<<ᵢ(op >>ᵢ $ 3) = vbity).
    { clear -Hrsl. funfold Hrsl. auto. }
   assert (Hvx_eq: (op&ᵢ$ 7) = vx).
    { clear -Hrsl. funfold Hrsl. auto. }
    assert (Hvbx_eq: $ 1<<ᵢ(op&ᵢ$ 7) = vbitx).
    { clear -Hrsl. funfold Hrsl. auto. }
  substs.
    (* prio ′ =ᶠ OS_EventTaskRdy (·pevent ′, 〈 (Void) ∗ 〉 NULL, 〈 Int8u 〉′OS_STAT_MUTEX·);ₛ*)
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).
  hoare_lifts_trms_pre Aop.
  Require Import hoare_forward_tac_ext.
  hoare forward.
2:{
(*   sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel 1%nat 2%nat. *)
  unfold AOSMapTbl.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AOSEventTbl.
  unfold node.
  sep cancel p_local.
  sep pauto.
  instantiate (17:= v'39).
  instantiate (15:= v'35).
  sep cancel (Aarray v'35).
  sep cancel (Astruct (v'39,Int.zero)).
  instantiate(10:= (DMutex (Vint32 x3) (Vptr (v'38,Int.zero)))).
  unfold AEventData in *.
  unfold V_OSEventType,V_OSEventCnt,V_OSEventPtr.
  simpl nth_val.
  sep pauto.
  sep_lift_context tcbdllseg.
  eapply tcbdllseg_compose.
  unfold tcbdllseg.
  instantiate (16:= v'3).
  unfold V_OSTCBPrev,V_OSTCBNext.
  sep cancel (dllseg v'3).
  instantiate (7:= 
  ( if Int.eq op (x3 >>ᵢ $ 8)
    then (vv
              :: v'13
                 :: x15
                    :: om
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                                :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                                   :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                                      :: Vint32 vmx :: Vint32 vmy :: nil)
    else (vv
              :: v'13
                 :: x15
                    :: om
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 op
                                :: Vint32 (op&ᵢ$ 7)
                                   :: Vint32 (op >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(op&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(op >>ᵢ $ 3)) :: nil) ) :: v'7).
  simpl dllseg.
  unfold node.
  sep pauto.
  instantiate (9:= vv).
  sep cancel (dllseg vv).
  instantiate (7:= v'38).
  instantiate (2:= (if Int.eq op (x3 >>ᵢ $ 8)
                                then (update_nth_val (Z.to_nat (Int.unsigned (x3 >>ᵢ $ 8)))
                                              (update_nth_val
                                                     (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2
                                                         (Vptr (v'38, Int.zero))) 
                                               (Vptr vhold_addr))
                                else (update_nth_val (Z.to_nat (Int.unsigned (x3 >>ᵢ $ 8))) v'2 (Vptr vhold_addr)) )).
  instantiate (3:= (if Int.eq op (x3 >>ᵢ $ 8) 
                                then (update_nth_val
                                              (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
                                                        (update_nth_val (Z.to_nat (Int.unsigned (op >>ᵢ $ 3))) v'8
                                                                                      (Vint32 (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7)))))
                                                        (Vint32 (Int.or vup vmx)))
                                else v'8 )).
  instantiate (2:= (if Int.eq op (x3 >>ᵢ $ 8) 
                                then ( if Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7))) ($ 0)
                                            then Vint32 (Int.or (i5&ᵢInt.not ($ 1<<ᵢ(op >>ᵢ $ 3))) vmy)
                                            else Vint32 (Int.or i5 vmy) )
                                else Vint32 i5)).
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  simpl val_inj in H58;
  eapply disj_split_star in H58;
  destruct H58;
   ssplit_apure_in H58;
   destruct H78; tryfalse;
   clear H78; try clear H79;
   sep cancel (Astruct (v'38, Int.zero));
   sep cancel (GAarray OSRdyTbl);
   sep cancel (GAarray OSTCBPrioTbl);
   sep cancel AOSPostEventTbl;
   [ destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7))) ($ 0)) eqn: eq3;
      simpl val_inj in H58;
      eapply disj_split_star in H58;
      destruct H58;
      ssplit_apure_in H58;
      destruct H78; tryfalse | idtac];
  sep cancel (Agvarmapsto OSRdyGrp); eauto.
(*   sep_lift_context_in H58 (aemp_isr_is);
  destruct s in*; destruct r in *;
  eapply aemp_isr_elim in H58;
  eauto. *)
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  simpl; auto.
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  simpl; auto.
  split;auto.
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  struct_type_match_solver.
  (* RL_Tbl_Grp_P *)
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2.
  2: { split; auto. }
  eapply inteqeq in eq2.
  subst op.
    destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))) ($ 0)) eqn: eq2.
    eapply return_rl_t_g_p; eauto.
    simpl. erewrite eq2. clear -H ; pure_auto.
    eauto.
    eapply return_rl_t_g_p'; eauto.
    simpl. erewrite eq2. simpl; auto.
    eauto.
  (* end of RL_Tbl_Grp_P *)
    assert (Hrange: Int.unsigned (Int.or (i5&ᵢInt.not ($ 1<<ᵢ(op >>ᵢ $ 3))) vmy) <= 255).
   { eapply int_unsigned_or_prop'; eauto. eapply int_lemma1; eauto. }
   assert (Hrange': Int.unsigned (Int.or i5 vmy) <= 255).
   { eapply int_unsigned_or_prop'; eauto. }
   destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
   try destruct (Int.eq (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7))) ($ 0)) eqn: eq3;
   simpl; clear -H67 Hrange Hrange'; pure_auto.

   destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2; split; auto.
   eapply array_type_vallist_match_hold;try rewrite update_nth_val_len_eq ; eauto.
   rewrite Hlrtbl. change (nat_of_Z OS_RDY_TBL_SIZE) with 8%nat. auto.
   simpl.
   assert (Hrange: Int.unsigned (Int.or vup vmx) <= 255) 
                by (eapply int_unsigned_or_prop'; eauto).
   clear -Hrange; pure_auto.
   do 2 rewrite update_nth_val_len_eq. auto. eauto.
   unfold V_OSPostEventGrp; simpl; auto.
   eauto. eauto. unfold V_OSEventGrp; simpl; auto. eauto. eauto.
   split;auto. struct_type_match_solver. 
  }
   2:{ split. unfold V_OSEventGrp; simpl; eauto. 
   eapply semacc_int_eq_false in eq1; change ($ 0) with Int.zero in eq1; auto. }
   2:{ instantiate (2:=(Vint32 (Int.modu ($ OS_STAT_MUTEX) ($ Byte.modulus))
         :: nil)).
    change ((Int.modu ($ OS_STAT_MUTEX) ($ Byte.modulus))) with ($ OS_STAT_MUTEX).
   simpl; eauto. }
   2: simpl; eauto.
   2: simpl; eauto.
    
  (* TCBList_P *)
  2:{
  sep_lift_context_in H58 (dllseg v'3).
  fold V_OSTCBNext in H58.
  fold V_OSTCBPrev in H58.
  fold tcbdllseg in H58.
  eapply tcbdllseg_get_last_tcb_ptr in H58.
  instantiate (1:= (if Int.eq op (x3 >>ᵢ $ 8) 
                                then (TcbMod.set v'11 (v'38, Int.zero)
                                                                    (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)) 
                                else v'11)).
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  try (eapply inteqeq in eq2; subst op);
  eapply TCBList_P_Combine; eauto.
  eapply TcbMod.joinsig_set_set; eauto.
  lets Hth: return_tcbl_p''.
  unfold and,or in Hth; simpl val_inj in Hth.
  eapply Hth;eauto.
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
  auto.
  Optimize Proof.
  Optimize Heap.
  lets Hth: return_tcbl_p_alt.
(*   lets Hth: return_tcbl_p''. *)
  unfold and,or in Hth; simpl val_inj in Hth.
  eapply Hth;eauto.
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
  auto. }
  (* end of TCBList_P *)
  (* R_ECB_ETbl_P *)
 2:{
   destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
   try eapply return_r_ecb_et_p; eauto. }
  (* R_PrioTbl_P *)
Open Scope code_scope.
 2:{
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  try (eapply inteqeq in eq2; subst op).
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
  assert (Hprio_ptbl_true: rule_type_val_match OS_TCB ∗ 
                                       (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = true).
   { eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
      rewrite H63. clear -Hprio_range'. auto with zarith. }
   lets Hptbl_prio: rule_type_val_match_ptr_elim Hprio_ptbl_true.
  assert (nth_val_ptbl:  (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = Vnull 
                                          \/ (nth_val' (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) = Vptr vhold_addr).
    {
        destruct Hptbl_prio as [Hnull | (pid & Hpid)]. auto.
        right.
        rewrite Hpid.
        assert (Hp: pid = vhold_addr \/ pid <> vhold_addr) by tauto.
        destruct Hp as [Hp | Hp]. subst pid; auto.
        eapply H49 in Hp; eauto.
        instantiate (1:= (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) in Hp.
        2 : { remember ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) as prio. clear -Hprio_range'. int auto. }
        2 : { unfold nat_of_Z. eapply nth_val'_imp_nth_val_vptr; eauto. }
        destruct Hp as (Hpst & Hpm & Hp).
        unfold RH_PrioTbl_P in H62. destruct H62 as (Hlh & Hhl).
        destruct Hhl as (Hhl1 & Hhl2 & Hhl3 & Hhl4 (* & Hhl5 *)).
        destruct Hop_neq as [Hnul | Hhold].
        eapply Hhl2 in Hnul. destruct Hnul as (Hr & Hn).
        clear -Hn Hpid. 
        change (nth_val
       ∘ (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))
       v'2) with (nth_val (Z.to_nat
            (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)))  v'2) in Hn.
        eapply nth_val'_imp_nth_val_vptr in Hpid. rewrite Hn in Hpid.
        inverts Hpid.
        eapply Hhl3 in Hhold. destruct Hhold as (Hr & Hn). 
        clear -Hn Hpid. 
        change (nth_val
       ∘ (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))
       v'2) with (nth_val (Z.to_nat (Int.unsigned (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8))) v'2) in Hn.
        eapply nth_val'_imp_nth_val_vptr in Hpid. rewrite Hn in Hpid.
        inverts Hpid. auto.
    }
    destruct nth_val_ptbl as [nth_vnull | nth_vhold];
    [ eapply return_r_pt_p'' | eapply return_r_pt_p]; eauto;
     try (eapply nth_val'_imply_nth_val; eauto);
     rewrite H63; clear -Hprio_range'; auto with zarith.
     eapply R_PrioTbl_P_update_vhold'; eauto.
      destruct Heqn; subst op; try rewrite Int.eq_true in eq2; tryfalse.
      destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
      2 : { eapply semacc_int_eq_false in eq2; tryfalse. }
      auto. }
    (* end of R_PrioTbl_P *)
    (* RL_RTbl_PrioTbl_P *)
2:{
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  try (eapply inteqeq in eq2; subst op).
  lets Hth: return_rl_rt_pt_p.
  unfold and,or in Hth; simpl val_inj in Hth.
  eapply Hth;eauto.
  eapply H64 in Hget_t. clear -Hget_t. destruct Hget_t. auto.
  eapply RL_RTbl_PrioTbl_P_update_vhold'; eauto.
  destruct Heqn; subst op; try rewrite Int.eq_true in eq2; tryfalse.
  destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
  2 : { eapply semacc_int_eq_false in eq2; tryfalse. }
  auto. }
  (* end of RL_RTbl_PrioTbl_P *)
2:{
   split;
   destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
   do 2 (try eapply array_type_vallist_match_hold; try rewrite update_nth_val_len_eq ; eauto);
   rewrite H63; clear -Hprio_range' Hpip_range; auto with zarith. }
   (* ptr_in_tcblist *)
 2:{ eapply tcblist_indom_ptr_in_tcblist.
     (* TCBList_P *)
  sep_lift_context_in H58 (dllseg v'3).
  fold V_OSTCBNext in H58.
  fold V_OSTCBPrev in H58.
  fold tcbdllseg in H58.
  eapply tcbdllseg_get_last_tcb_ptr in H58.
  instantiate (2:= (if Int.eq op (x3 >>ᵢ $ 8)
   then
    update_nth_val (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
      (update_nth_val (Z.to_nat (Int.unsigned (op >>ᵢ $ 3))) v'8
         (Vint32 (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7))))) (Vint32 (Int.or vup vmx))
   else v'8)).
  instantiate (1:= (if Int.eq op (x3 >>ᵢ $ 8) 
                                then (TcbMod.set v'11 (v'38, Int.zero)
                                                                    (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)) 
                                else v'11)).
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  try (eapply inteqeq in eq2; subst op);
  eapply TCBList_P_Combine; eauto.
  eapply TcbMod.joinsig_set_set; eauto.
  lets Hth: return_tcbl_p''.
  unfold and,or in Hth; simpl val_inj in Hth.
  eapply Hth;eauto.
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
  auto.
  lets Hth: return_tcbl_p_alt.
  unfold and,or in Hth; simpl val_inj in Hth.
  eapply Hth;eauto.
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
  auto.
  (* end of TCBList_P *)
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
  unfold indom.
  rewrite TcbMod.map_get_set. eauto.
  unfold get. unfold TcbMap.
  rewrite Hget_t. eauto. }
  (* end of ptr_in_tcblist *)
  2: pure_auto.
  (* retpost OS_EventTaskRdyPost *)
  2:{ apply retpost_eventrdy. }
  3:{ intros. do 27 destruct H58.  eexists. instantiate (1:= (logic_val (V$ 1) :: x33)). sep pauto. }
  3:{ intros. do 20 destruct H58.  eexists.  instantiate (1:= (logic_val (V$ 1) :: x26)). sep pauto. }
  (* end of OS_EventTaskRdy *)
  2:{ simpl. unfold OS_STAT_MUTEX. pure_auto. }
  change ((Int.modu ($ OS_STAT_MUTEX) ($ Byte.modulus))) with ($ OS_STAT_MUTEX).
  unfold OS_STAT_MUTEX.
  simpl.  splits; eauto.
  destruct_s s. simpl; auto.
  destruct_s s. simpl; auto.
  unfold OS_EventTaskRdyPost.
  unfold OS_EventTaskRdyPost'.
  unfold getasrt.
  change ((Int.modu ($ OS_STAT_MUTEX) ($ Byte.modulus))) with ($ OS_STAT_MUTEX) in *.
  simpl nth_val.
  hoare unfold.
  inverts H104.
  simpl update_nth_val in H113.
  eapply nth_upd_eq in H108.
  subst v'89.
  simpl rel_edata_tcbstat in H81.
(*   subst v'76.
  try rewrite Int.and_not_self in *. *)

  lets Hvl_match: H114.
  simpl in H114.
  destruct H114 as (Htp_range & Hgrp_range & Hx1_range & _ & _ & _).
  eapply int_true_le255 in Htp_range.
  eapply int_true_le255 in Hgrp_range.
  rewrite ifE in Hx1_range.
  eapply leb_int16max_true_elim in Hx1_range.
  lets Hx1_range_and: acpt_int_lemma00 x3.
  lets Hv63_range: math_unmap_get_y H23 H82.
  rename H20 into Hltbl.
  assert (Hv63_range': (Z.to_nat (Int.unsigned v'69) < length v'49)%nat).
  {
    rewrite Hltbl.
    clear -Hv63_range. change (∘ OS_EVENT_TBL_SIZE)  with 8%nat.
    auto with zarith.
  }
  lets Hv64_true: array_type_vallist_match_imp_rule_type_val_match Hv63_range' H13.
  rewrite H83 in Hv64_true.
  assert (Hv64_range: Int.unsigned v'70 <= 255).
  {
    eapply rule_type_val_match_int8u_elim in Hv64_true.
    clear -Hv64_true.
    mytac. inverts H. auto.
  }
  rename v'48 into grp. rename v'49 into rtbl.
  assert (Hwait: PrioWaitInQ (Int.unsigned ((v'69<<ᵢ$ 3) +ᵢ  v'68)) rtbl ).
  {
    eapply prio_from_grp_tbl_PrioWaitInQ; eauto.
    eapply semacc_int_eq_false; eauto.
  }
  assert (Hwait_range: (Int.unsigned ((v'69<<ᵢ$ 3) +ᵢ  v'68)) < 64).
  {
    clear -Hwait. funfold Hwait. auto.
  }
  assert (Hwait_range': (Int.unsigned ((v'69<<ᵢ$ 3) +ᵢ  v'68)) <= 255).
  { clear -Hwait_range.   auto with zarith. }

  (* get same pre condition*)
  lets Hgrp_nzero: semacc_int_eq_false eq1.
  lets Hv62_range: math_unmap_get_y Hv64_range H84.
  lets Hrptbl_new : H101.
  destruct Hrptbl_new as (Hrptbl_new & _ & _).
  assert (Hwait_get_t: exists b c d, 
                              TcbMod.get (if Int.eq op (x3 >>ᵢ $ 8)
                                                    then TcbMod.set v'11 (v'38, Int.zero) (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)
                                                    else v'11) (v'86, Int.zero) = Some (((v'69<<ᵢ$ 3) +ᵢ  v'68), b, c, d)).
 { eapply Hrptbl_new; eauto.
    split; auto.
    remember ((v'69<<ᵢ$ 3) +ᵢ  v'68) as pw.
    clear -H. int auto.
    unfold nat_of_Z.
    eapply nth_val'_imply_nth_val; eauto.
    destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
    rewrite update_nth_val_len_eq; try rewrite update_nth_val_len_eq;
    rewrite H63; clear -Hwait_range; auto with zarith.
  }
  destruct Hwait_get_t as (wait_st & wait_m & wait_sus & Hwait_get_t).
   lets Hwait_tcj: TcbMod.map_join_get_sig Hwait_get_t.
   destruct Hwait_tcj as (wait_tls1 & Hwait_tcj).
   assert (Hnew_rh_tbl_ebl_p: RH_TCBList_ECBList_P els
                                                    (if Int.eq op (x3 >>ᵢ $ 8)
                                                     then TcbMod.set v'11 (v'38, Int.zero) (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)
                                                     else v'11) (v'38, Int.zero)).
  { destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
     try (eapply inteqeq in eq2; subst);
     try eapply RH_TCBList_ECBList_P_post_changeprio';eauto.
     destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
     clear -Hlt_pip Hop_eq.
     eapply ltu_eq_false in Hlt_pip.
    rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse. 
    auto. }
(*       try eapply RH_TCBList_ECBList_P_changeprio'; eauto. } *)
  assert (Hwait_cond: ((v'69<<ᵢ$ 3) +ᵢ  v'68) = ((v'69<<ᵢ$ 3) +ᵢ  v'68) /\ w <> nil /\
                            GetHWait (if Int.eq op (x3 >>ᵢ $ 8)
                                                then TcbMod.set v'11 (v'38, Int.zero) (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)
                                                else v'11) w (v'86, Int.zero) /\
                            TcbMod.get (if Int.eq op (x3 >>ᵢ $ 8)
                                                    then TcbMod.set v'11 (v'38, Int.zero) (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)
                                                    else v'11) (v'86, Int.zero) = Some (((v'69<<ᵢ$ 3) +ᵢ  v'68), wait_st, wait_m, wait_sus)).
  { eapply post_exwt_succ_pre_mutex; eauto.
     clear -Hv63_range. auto with zarith.
     clear -Hv62_range. auto with zarith. }
  destruct Hwait_cond as (_ & Hwait_neq_nil & Hwait_gethw & Hhtcb_get).
  assert (Hwait_in: In (v'86, Int.zero) w).
  { clear -Hwait_gethw. funfold Hwait_gethw. auto. }
  assert (Hwait_st: exists prio msg wait_time wait_sus, 
                                              get (if Int.eq op (x3 >>ᵢ $ 8)
                                                    then TcbMod.set v'11 (v'38, Int.zero) (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8, rdy, om, false)
                                                    else v'11) (v'86, Int.zero) 
                                            = Some (prio, wait (os_stat_mutexsem (v'92,Int.zero)) wait_time, msg, wait_sus) ).
  { destruct Hnew_rh_tbl_ebl_p as (_ & _ & _ & Hnew_rh_tbl_ebl_p).
    eapply Hnew_rh_tbl_ebl_p. split; eauto.
  }
  destruct Hwait_st as (ep & em & ewt & esus & Hwait_st).
  unfold get in Hwait_st; unfold TcbMap in Hwait_st.
  rewrite Hwait_get_t in Hwait_st. inverts Hwait_st.
  assert (Hwait_neq_ct: (v'38, Int.zero) <> (v'86, Int.zero)).
  { pure_auto.
    inverts H20.
    clear -Hwait_get_t Hget_t.
    destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
    try rewrite TcbMod.map_get_set in Hwait_get_t;
    try rewrite Hget_t in Hwait_get_t;
    inverts Hwait_get_t.
  }
  assert (Hwait_get_t' : TcbMod.get v'11 (v'86, Int.zero) =
                                        Some ((v'69<<ᵢ$ 3) +ᵢ  v'68, wait (os_stat_mutexsem (v'92, Int.zero)) ewt, em, esus)).
  { clear -Hwait_get_t Hwait_neq_ct.
     destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2; auto.
      eapply TcbMod.map_get_set' in Hwait_neq_ct.
      erewrite Hwait_neq_ct in Hwait_get_t.
      auto.
  Optimize Proof.
  Optimize Heap.
  }

  (* set_node process *)
    assert (Hv63_eq: (((v'69<<ᵢ$ 3) +ᵢ  v'68) >>ᵢ $ 3) = v'69).
    { eapply math_shrl_3_eq; eauto.
      clear -Hv63_range' Hltbl.
      rewrite Hltbl in Hv63_range'.
      change (∘ OS_EVENT_TBL_SIZE) with 8%nat in *.
     auto with zarith.
    }
    assert (Hv63_range'': (Z.to_nat (Int.unsigned v'69) <
 length
   (if Int.eq op (x3 >>ᵢ $ 8)
    then
     update_nth_val (Z.to_nat (Int.unsigned ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)))
       (update_nth_val (Z.to_nat (Int.unsigned (op >>ᵢ $ 3))) v'8
          (Vint32 (rrow&ᵢInt.not ($ 1<<ᵢ(op&ᵢ$ 7))))) (Vint32 (Int.or vup vmx))
    else v'8))%nat).
  { destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2;
       try repeat rewrite update_nth_val_len_eq;
       rewrite Hlrtbl; change (∘ OS_RDY_TBL_SIZE) with 8%nat;
       clear -Hv63_range; auto with zarith.
   }
  lets Hv81_range: array_int8u_nth_lt_len H91 Hv63_range''.
  destruct Hv81_range as (new_rrow & Hv81_eq & Hnew_rrow_range).
  rewrite H58 in Hv81_eq. inverts Hv81_eq.
  assert (Hv62_eq: (((v'69<<ᵢ$ 3) +ᵢ  v'68)&ᵢ$ 7) = v'68).
  { eapply math_8range_eqy; eauto. clear -Hv63_range. auto with zarith. }
  lets Hv65_eq: math_mapval_core_prop Hv62_range H86.
    Require Import tcblist_setnode_lemmas.
  
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P H103 H77 Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  destruct Htmp as (Hmsg & Htprio & Hh_tcbblk & Hh_tcbstat).
  inverts Hmsg; inverts Htprio.

(*   unfolds in Hh_tcbblk.
  mytac.
  inverts H44. 
  inverts H45. inverts H53. inverts H68. inverts H69. inverts H75. inverts H82.
  inverts H61. *)

    eapply backward_rule1.
    introv Hsat.
    sep_lift_context_in Hsat (tcbdllseg).

    eapply set_node_elim_sus; eauto.
    eapply TCBNode_P_set_rdy_gen; auto.
    2:eauto.
     split; auto.
    remember ((v'69<<ᵢ$ 3) +ᵢ  v'68) as pw. clear -H; int auto.
    rewrite Hv63_eq.
    eapply nth_val'_imply_nth_val; eauto. auto.
    2:{
    eapply TCBList_P_tcblist_get_TCBNode_P; eauto. }
    destruct H81; subst v'80.
    assert (Hsus: esus = false). 
     eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; tauto.
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: esus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; tauto).
    subst.
    change (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_MUTEX)) with ($ OS_STAT_SUSPEND).
    auto.
    destruct esus eqn: eq3; auto.
    unfold rtbl_set_one_bit.
    repeat eexists; try rewrite Hv63_eq; try rewrite Hv62_eq; try rewrite <- Hv65_eq; eauto.
    remember ((v'69<<ᵢ$ 3) +ᵢ  v'68) as pw. clear -H; int auto. 
    destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2; eauto.
    destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
    subst op.
    eapply R_Prio_No_Dup_hold_gen; eauto.
    eapply inteqeq in eq2.
    eapply ltu_eq_false in Hlt_pip. rewrite eq2; eauto.
    eapply R_Prio_No_Dup_hold_ptls_gen'; eauto.
    clear -H.
    unfold same_prev_next.
    unfold V_OSTCBNext,V_OSTCBPrev. simpl. auto.
    hoare unfold.
    (* get the relation between the highest TCB priority in wait list and Mutex prio-ceiling *)
    assert (Hwait_gethw':  GetHWait v'11 w (v'86, Int.zero)).
  { destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2; auto.
     eapply return_gethwait; eauto. }

    assert (Hwait_hp_case: Int.ltu (x3 >>ᵢ $ 8) ((v'69<<ᵢ$ 3) +ᵢ  v'68) = false
                                              \/ Int.ltu (x3 >>ᵢ $ 8) ((v'69<<ᵢ$ 3) +ᵢ  v'68) = true ).
    { clear -H. destruct (Int.ltu (x3 >>ᵢ $ 8) ((v'69<<ᵢ$ 3) +ᵢ  v'68)); auto. }
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid).
    destruct Hwait_hp_case as [Hwait_abt | Hwait_hp].
    {
       eapply abscsq_rule.
       apply noabs_oslinv.
       eapply mutexpost_absimp_wl_highest_prio_err_abt'; eauto.
       can_change_aop_solver. eapply absinfer_eq.
       apply absabort_rule.
     }

  (* pevent ′ → OSEventCnt &= ′ OS_MUTEX_KEEP_UPPER_8;ₛ *)
  hoare forward.
  (* pevent ′ → OSEventCnt =ₑ pevent ′ → OSEventCnt |ₑ prio ′;ₛ *)
  hoare forward.
  struct_type_match_solver.
  clear -Hwait_range'. pure_auto.
  (* pevent ′ → OSEventPtr =ₑ OSTCBPrioTbl ′ [prio ′];ₛ *)
  hoare forward.
  clear -Hwait_range'. pure_auto.
  rewrite H76.
  simpl; auto.

  (* split 2 cases before EXIT_CRITICAL;ₛ *)
  destruct (Int.eq op (x3 >>ᵢ $ 8)) eqn: eq2.
  (* case3 : OSTCBCur->OSTCBPrio = pip /\ pevent->OSEventGrp <> 0 *)
  eapply inteqeq in eq2.
  subst op.
  destruct Hp_case as [(Hop_eq & _) | (_ & Hop_neq & Hpr_no_use) ].
  clear -Hlt_pip Hop_eq.
  eapply ltu_eq_false in Hlt_pip.
  rewrite Hop_eq in Hlt_pip; rewrite Int.eq_true in Hlt_pip; tryfalse.

  assert (Hopv: opv = V$ OS_NO_ERR \/ opv <> V$ OS_NO_ERR) by (clear -H; tauto).
  hoare_lifts_trms_pre ( absecblsid, abstcblsid, ostmid, curtid, absptlsid).
  mytac_lift_absop.
  destruct Hopv as [Hopv | Habt].
  2 : {  eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexpost_absimp_exwt_return_prio_succ_abt'; eauto.
           can_change_aop_solver. eapply absinfer_eq.
           apply absabort_rule.
        }
  subst opv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutexpost_absimp_exwt_return_prio_succ'; eauto.
  can_change_aop_solver. eapply absinfer_eq.
  (* EXIT_CRITICAL;ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais;(*  sep cancel Aier; *) sep cancel aemp_isr_is). 
  Require Import hoare_forward_tac_ext.
  hoare forward prim.
  
  (* RH_CurTCB *)
  2: { unfold RH_CurTCB.
         rewrite TcbMod.set_sem.
         rewrite TcbMod.map_get_set.
         destruct (tidspec.beq (v'86, Int.zero) (v'38, Int.zero)); eauto.
        }
  (* RH_TCBList_ECBList_P *)
  2: { eapply rh_tcblist_ecblist_p_post_exwt_mutex' with (x:= (x3 >>ᵢ $ 8)); try erewrite TcbMod.map_get_set; eauto. }
  unfold AOSTCBPrioTbl.
  sep pauto; eauto.
  sep cancel (Aptrmapsto vhold_addr).
  sep cancel (Agvarenv' OSPlaceHolder).
  (* R_PrioTbl_P *)
  3 : { eapply r_priotbl_p_set_hold; eauto. }
  unfold AOSTCBList.
  sep cancel Aier.
  sep pauto; eauto. 
  sep cancel (tcbdllseg v'57).
  sep cancel (tcbdllseg (Vptr (v'38, Int.zero))).
  sep_lift_context tcbdllflag.
  eapply tcbdllflag_set_node; eauto.
  eapply tcbdllflag_hold;  try sep cancel tcbdllflag.
  eapply tcbdllflag_hold_middle.
  simpl eq_dllflag.
  unfold V_OSTCBNext,V_OSTCBflag.
  simpl. auto.
  2: { clear -H. unfold same_prev_next.
         unfold V_OSTCBNext,V_OSTCBPrev. simpl. auto. }
  unfold EvtInv. unfold AECBList.
  sep pauto.
  eapply lzh_evsllseg_compose.
  sep cancel (evsllseg v'10).
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep split; try sep cancel Aarray; auto.
  instantiate (18:= v'92).
  sep cancel (Astruct (v'92, Int.zero)).
  rewrite H76.
  instantiate (13 := (DMutex (Vint32 (Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((v'69<<ᵢ$ 3) +ᵢ  v'68))) 
                                                  (Vptr (v'86, Int.zero)))).
  simpl AEventData in *.
  unfold V_OSEventType,V_OSEventCnt,V_OSEventPtr.
  simpl nth_val.
  sep pauto; auto.
(*   2 : { sep_lift_context_in H80 Aier. eapply astar_l_aier_elim in H80.
           destruct H80. eauto. } *)
  2: eauto.
  2 : { unfold V_OSPostEventGrp; simpl; eauto. }
  5: { splits; auto.  rewrite H76.
          lets Hor_range: mund_int_c1 Hwait_range H24. 
           struct_type_match_solver.  }
    2: { eauto. } 
    4:{ unfold V_OSEventListPtr; simpl; eauto. }
    3:{ unfold V_OSEventGrp; simpl; eauto. }
   3: { eauto. }
   3: { eauto. }
  (* ECBList_P *)
  6 : {   rewrite H76. 
          eapply ecblist_p_post_exwt_hold_mutex_new'; eauto.
          clear -Hv63_range. auto with zarith.
          clear -Hv62_range. auto with zarith.
          eapply exists_some_unmap_is_x; eauto.
          Require Import Mbox_common.
          eapply R_ECB_PETbl_P_set_tcb_wait_hold; eauto.
          unfolds. introv Hv. destruct Hv as (qid & tm & Hr). inverts Hr.
          eapply ecblist_p_mutexpend_changeprio; eauto.
          eapply ecblist_p_mutexpend_changeprio; eauto.
       }
    sep cancel p_local.
    sep cancel AOSPostEventTbl.
    sep_lift_context_in H80 ASemEIBs.
    eapply ASemEIBs_set_ow_preserve in H80; eauto. 
    sep_lift_context_in H80 AMqEIBs.
    eapply AMqEIBs_set_ow_preserve in H80; eauto.
    sep cancel AMqEIBs. sep cancel ASemEIBs. eauto.
    sep_lift_context_in H80 AMuxEIBs.
    eapply AMuxEIBs_set_ow_preserve in H80; eauto.
    sep cancel AMuxEIBs. unfold tcbllsegevaux in *.
    sep cancel AOSEventFreeList. sep cancel AOSQFreeList.
    sep cancel AOSQFreeBlk.
    
    eapply  llsegevaux_set_node. sep_lift_context_in H80 llsegevaux.
    2:{ eauto. }  
(*   sep_lifts_trms_in H80 Aier.
  eapply astar_l_aier_elim in H80. destruct H80. *)
    eapply llsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
    sep cancel llsegevaux. cancel_corecommuinv. 
    cancel_partitioninv.
    eauto.
    eapply tcb_linked_list_same_next_split.
    eapply tcb_linked_list_same_next_self; eauto.
    rewrite <- nil_simp.
   change ((vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7) with (nil ++ (vv
    :: v'13
       :: x15
          :: om
             :: V$ 0
                :: V$ OS_STAT_RDY
                   :: Vint32 (x3 >>ᵢ $ 8)
                      :: Vint32 ((x3 >>ᵢ $ 8)&ᵢ$ 7)
                         :: Vint32 ((x3 >>ᵢ $ 8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ((x3 >>ᵢ $ 8)&ᵢ$ 7))
                               :: Vint32
                                    ($ 1<<ᵢ((x3 >>ᵢ $ 8) >>ᵢ $ 3))
                                  :: nil) :: v'7).
    eapply tcb_linked_list_same_next_mid; eauto. eauto.
    unfolds; simpl; eauto.
    2: eapply mq_ecb_p_mux_set_preserve; eauto.
    2: eapply mux_ecb_p_mux_set_preserve; eauto.
    2: eapply sem_ecb_p_mutex_set_preserve; eauto.
    eauto.
    3:{     eapply RH_PrioTbl_P_update_vhold; eauto.
    clear -Hpip_range. split; auto. apply Int.unsigned_range_2.
  eapply RH_PrioTbl_P_update_tcb; eauto.   
  clear -Hprio_range'. unfold OS_MUTEX_KEEP_LOWER_8.  splits; eauto; int auto. 
  eapply Z_land_range_lo_r; int auto. eapply Z_land_range; int auto. 
  unfold OS_MUTEX_KEEP_LOWER_8. auto with zarith.
  eapply Z_land_range; eapply Int.unsigned_range_2. auto.
  auto.  eapply H64 in Hget_t. destruct Hget_t; auto. } eauto. 

  
    destruct H81; subst v'80.
      rewrite Hv63_eq in *. rewrite Hv62_eq in *.
    assert (Hsus: esus = false). 
    eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; tauto.
    subst.
    rewrite Int.and_not_self; auto.
    change (Int.eq Int.zero ($ OS_STAT_RDY)) with true.
    assert (Hsus: esus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; tauto).
    subst.
    change (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_MUTEX)) with ($ OS_STAT_SUSPEND).
    auto.
  Optimize Proof.
  Optimize Heap.
    destruct H81; subst v'80.
    rewrite Hv63_eq in *. rewrite Hv62_eq in *.
    assert (Hsus: esus = false). 
    eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; tauto.
    subst.
    rewrite Int.and_not_self; auto.
    change (Int.eq Int.zero ($ OS_STAT_RDY)) with true.
    assert (Hsus: esus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; tauto).
    subst.
    change (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_MUTEX)) with ($ OS_STAT_SUSPEND).
    auto.

  pure_auto.

  hoare forward.
  unfolds. left; auto.
  pure_auto.
(*     sep cancel p_local.
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Acs.
    sep cancel Aisr.
    sep cancel 1%nat 1%nat.
    eauto.
    unfold isflag. auto.
    pure_auto. *)
    intros. eexists.  sep pauto. inverts H87.
    sep cancel p_local.
    sep pauto.
    
    intros. sep pauto. inverts H87.
 instantiate (1:= (logic_val x5
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val (Vptr (v'92, Int.zero))
                  :: logic_val Vnull :: logic_val Vnull :: nil)).
    sep pauto.
    unfold OS_SchedPost.
    unfold OS_SchedPost'.
    unfold getasrt.
    hoare unfold.
    inverts H80.
    (* RETURN *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_seq_end; eauto; can_change_aop_solver.
    hoare forward.
    intros. simpl in H81. tryfalse.
    splits; eauto.
    change (Int.unsigned ($ OS_NO_ERR)) with 0.
    auto with zarith.
    (* end of case3 *)

   (* case4 : OSTCBCur->OSTCBPrio <> pip /\ pevent->OSEventGrp <> 0 *)
    destruct Heqn; subst op; try rewrite Int.eq_true in eq2; tryfalse.
    destruct Hp_case as [(Hp1 & Hneq) | (Hp2 & Hneq & Hpr_no_use)].
    2 : { eapply semacc_int_eq_false in eq2; tryfalse. }
    assert (Hopv: opv = V$ OS_NO_ERR \/ opv <> V$ OS_NO_ERR) by (clear -H; tauto).
    destruct Hopv as [Hopv | Habt].
    2 : {
           hoare_lifts_trms_pre (absecblsid, abstcblsid, ostmid, curtid, absptlsid).
            mytac_lift_absop.
            eapply abscsq_rule.
           apply noabs_oslinv.
           eapply mutexpost_absimp_exwt_no_return_prio_succ_abt'; eauto.
           can_change_aop_solver. eapply absinfer_eq.
           apply absabort_rule.
        }
    subst opv.
    hoare_lifts_trms_pre (absecblsid, abstcblsid, ostmid, curtid, absptlsid).
    mytac_lift_absop.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutexpost_absimp_exwt_no_return_prio_succ'; eauto.
    can_change_aop_solver. eapply absinfer_eq.
    (* EXIT_CRITICAL *)
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr; sep cancel Ais;(*  sep cancel Aier; *) sep cancel aemp_isr_is). 
    hoare forward prim.
    (* RH_CurTCB *)
  2: { unfold RH_CurTCB.
         rewrite TcbMod.set_sem.
         destruct (tidspec.beq (v'86, Int.zero) (v'38, Int.zero)); eauto.
        }
  (* RH_TCBList_ECBList_P *)
  2: {  eapply rh_tcblist_ecblist_p_post_exwt_mutex' with (x:= (x3 >>ᵢ $ 8)) (t:= (v'38, Int.zero)); try erewrite TcbMod.map_get_set; eauto. }
    unfold AOSTCBPrioTbl.
    sep pauto; eauto.
    (* R_PrioTbl_P *)
  3 : { eapply r_priotbl_p_set_hold; eauto. }
   (*RH_PrioTbl_P*)
  2 : { eapply RH_PrioTbl_P_update_vhold; eauto.
    clear -Hpip_range. split; auto. apply Int.unsigned_range_2. }
    sep cancel (Aptrmapsto vhold_addr).
    sep cancel (Agvarenv' OSPlaceHolder).
    unfold AOSTCBList.
    sep pauto; eauto.
    sep cancel (tcbdllseg v'57).
    sep cancel (tcbdllseg (Vptr (v'38, Int.zero))).
    sep cancel APthreadAttr.
  sep cancel CapabilityInv.
    sep_lift_context tcbdllflag.
    eapply tcbdllflag_set_node; eauto.
    eapply tcbdllflag_hold;  try sep cancel tcbdllflag.
    eapply tcbdllflag_hold_middle.
    simpl eq_dllflag.
    unfold V_OSTCBNext,V_OSTCBflag.
    simpl. auto.
    2: { clear -H. unfold same_prev_next.
         unfold V_OSTCBNext,V_OSTCBPrev. simpl. auto. }
  unfold EvtInv.
  unfold AECBList.
  sep pauto.
  eapply lzh_evsllseg_compose.
  sep cancel (evsllseg v'10).
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep normal.
  sep eexists.
  sep split; try sep cancel Aarray; auto.
  sep cancel p_local.
  instantiate (17:= v'92).
  sep cancel (Astruct (v'92, Int.zero)).
  rewrite H76.
  instantiate (12 := (DMutex (Vint32 (Int.or (x3&ᵢ$ OS_MUTEX_KEEP_UPPER_8) ((v'69<<ᵢ$ 3) +ᵢ  v'68))) 
                                                  (Vptr (v'86, Int.zero)))).
  simpl AEventData in *.
  unfold V_OSEventType,V_OSEventCnt,V_OSEventPtr.
  simpl nth_val.
  sep pauto; auto.
  2:{  sep_lift_context_in H80 Aier. eapply astar_l_aier_elim in H80.
           destruct H80. eauto. }
  2 : { eauto. }
  2 : { unfold V_OSPostEventGrp; simpl; eauto. }
  2 : { eauto. }
  3 : { unfold V_OSEventGrp; simpl; eauto. } 
  2 : { eauto. }
  2: { splits; auto. rewrite H76.
           lets Hor_range: mund_int_c1 Hwait_range H24.
           struct_type_match_solver.  }
    2: { unfold V_OSEventListPtr; simpl; eauto. }
   2: { eauto. }
   2: { eauto. }
   (* ECBList_P *)
  5 : { rewrite H76.
          eapply ecblist_p_post_exwt_hold_mutex_new'; eauto.
          clear -Hv63_range. auto with zarith.
          clear -Hv62_range. auto with zarith.
          eapply exists_some_unmap_is_x; eauto.
       }
    sep cancel AOSPostEventTbl.
    sep cancel AOSEventFreeList.
    sep cancel AOSQFreeList.
    sep cancel AOSQFreeBlk.
    unfold AMuxEIBs in *.
    sep pauto; eauto.
    sep cancel APthreadMutex.
    sep_lift_context_in H80 ASemEIBs.
    eapply ASemEIBs_set_ow_preserve in H80; eauto. 
    sep_lift_context_in H80 AMqEIBs.
    eapply AMqEIBs_set_ow_preserve in H80; eauto.
    sep cancel AMqEIBs. sep cancel ASemEIBs. eauto.
    sep cancel AMuxCap.
    unfold tcbllsegevaux in *.
    eapply  llsegevaux_set_node. sep_lift_context_in H80 llsegevaux.
    2:{ eauto. } 
    sep_lifts_trms_in H80 Aier.
    eapply astar_l_aier_elim in H80. destruct H80.
    eapply llsegevaux_tcbvl_tcb_linked_list_same_next_preserve; eauto.
    sep cancel llsegevaux. cancel_corecommuinv. 
    cancel_partitioninv.
    eauto.
    eapply tcb_linked_list_same_next_split.
    eapply tcb_linked_list_same_next_self; eauto.
    rewrite <- nil_simp.
    change ((vv
    :: v'13 :: x15 :: om
             :: V$ 0  :: V$ OS_STAT_RDY
                   :: Vint32 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                      :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                         :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) &ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ ((x3&ᵢ $ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) :: nil) :: v'7) with 
    (nil ++(vv
    :: v'13 :: x15 :: om
             :: V$ 0  :: V$ OS_STAT_RDY
                   :: Vint32 (x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)
                      :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8)&ᵢ$ 7)
                         :: Vint32 ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ ((x3&ᵢ$ OS_MUTEX_KEEP_LOWER_8) &ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ ((x3&ᵢ $ OS_MUTEX_KEEP_LOWER_8) >>ᵢ $ 3)) :: nil) :: v'7).
    eapply tcb_linked_list_same_next_mid; eauto. eauto.
    unfolds; simpl; eauto.
    eapply RH_ECBlk_EIBlk_Mux_P_set_op; eauto.
    eapply mq_ecb_p_mux_set_preserve; eauto.
    eapply mux_ecb_p_mux_set_preserve; eauto.
    eapply sem_ecb_p_mutex_set_preserve; eauto.
    destruct H81; subst v'80.
      rewrite Hv63_eq in *. rewrite Hv62_eq in *.
    assert (Hsus: esus = false). 
    eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; tauto.
    subst.
    rewrite Int.and_not_self; auto.
    change (Int.eq Int.zero ($ OS_STAT_RDY)) with true.
    assert (Hsus: esus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; tauto).
    subst.
    change (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_MUTEX)) with ($ OS_STAT_SUSPEND).
    auto.
  Optimize Proof.
  Optimize Heap.
    destruct H81; subst v'80.
    rewrite Hv63_eq in *. rewrite Hv62_eq in *.
    assert (Hsus: esus = false). 
    eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; tauto.
    subst.
    rewrite Int.and_not_self; auto.
    change (Int.eq Int.zero ($ OS_STAT_RDY)) with true.
    assert (Hsus: esus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; tauto).
    subst.
    change (Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_MUTEX)) with ($ OS_STAT_SUSPEND).
    auto.

    pure_auto.
    (* end of EXIT_CRITICAL *)
    (* OS_Sched *)
    Require Import hoare_forward_tac_ext.
    hoare forward.
    unfold isflag. auto.
    pure_auto.
    intros. eexists.  sep pauto. inverts H87. sep cancel p_local. 
    sep pauto.
    intros. sep pauto. inverts H87.
    instantiate (1:= (logic_val x5
            :: logic_val (V$ os_code_defs.__EvLoc_normal)
               :: logic_val (Vptr (v'92, Int.zero))
                  :: logic_val Vnull :: logic_val Vnull :: nil)).
    sep pauto.
    unfold OS_SchedPost.
    unfold OS_SchedPost'.
    unfold getasrt.
    hoare unfold.
    inverts H80.
    (* RETURN *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_seq_end; eauto; can_change_aop_solver.
    hoare forward.
    intros. simpl in H81. tryfalse.
    splits; eauto.
    change (Int.unsigned ($ OS_NO_ERR)) with 0.
    auto with zarith.
    (* end of case4 *)
  Unshelve.
  exact (Int.zero).
  exact (Int.zero).
  exact (Vint32 Int.zero).
  exact (Vint32 Int.zero).
  exact nil.
Qed.


