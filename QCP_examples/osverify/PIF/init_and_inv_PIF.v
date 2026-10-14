Require Import PIF_sys.
(* Require Import PIF_succs. *)
Require Import PIF_spec.
Require Import PIF_os_mutex_cap.
Require Import PIF_language.
Require Import PIF_Modules.
Require Import List.
Require Import PIF_opsem.
Require Import Maps.
Require Import PIF_memory.

Require Import mux_succ_gen. 

(*defination of UPIF*)
Definition WAIT_OWNER t t_owner tls els:=
  exists qid p v m p_owner wl p_q sus,
    TcbMod.get tls t = Some (p,wait (os_stat_mutexsem qid) v,m, sus) /\
    EcbMod.get els qid = Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Inductive WAIT_CHAIN: tid -> tid -> TcbMod.map ->  EcbMod.map -> Prop :=
| wait_O: forall t t_owner tls els, WAIT_OWNER t t_owner tls els /\ t <> t_owner  ->
                     WAIT_CHAIN t t_owner tls els
| wait_S: forall t t_owner tls els t', WAIT_OWNER t t' tls els -> WAIT_CHAIN t' t_owner tls els ->
                     WAIT_CHAIN t t_owner tls els.

Definition IS_OWNER t_owner qid els :=
  exists p_q p_owner wl, EcbMod.get els qid =  Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Definition IS_NOT_OWNER t els :=
  ~ exists eid, IS_OWNER t eid els.

Definition IS_OWNER_P t_owner qid els p_owner:=
  exists p_q wl, EcbMod.get els qid =  Some (absmutexsem p_q (Some (t_owner,p_owner)),wl).

Definition ST_WAIT_T t els:=
  exists qid p_q owner wl, 
   EcbMod.get els qid =  Some (absmutexsem p_q owner,wl) /\ 
   In t wl.

Definition IS_WAITING_E t eid els:=
  exists p_q owner wl, EcbMod.get els eid =  Some (absmutexsem p_q owner,wl) /\ In t wl.

Definition HighestRdy tls t :=
  exists prio msg0 sus,
    TcbMod.get tls t = Some (prio, rdy, msg0, sus) /\
    (forall (i : tid) (prio' : priority) (msg' : msg) sus',
       i <> t ->
       TcbMod.get tls i = Some (prio', rdy, msg', sus') ->
       Int.ltu prio prio' = true).
Definition GET_ORP t tls els p :=
  TcbMod.get tls t <> None ->
  (exists qid, IS_OWNER_P t qid els p) \/
  ((~ exists qid, IS_OWNER t qid els) /\ exists st msg sus, TcbMod.get tls t = Some (p,st,msg,sus)).

Definition UPIF (O:osabst) :=
  forall els tls ct p_ct mls pls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    OSAbstMod.get O absmutinfoid = Some (absmutinfo mls) ->
    OSAbstMod.get O absptlsid = Some (absptls pls) ->
    GET_ORP ct tls els p_ct ->
    HighestRdy tls ct ->
    ~ (exists eid, IS_OWNER ct eid els)  ->
    forall t p_t,
      t <> ct ->
      TcbMod.get tls t <> None ->
      GET_ORP t tls els p_t ->
      (exists t', WAIT_CHAIN t t' tls els) ->
      Int.ltu p_ct p_t = true \/ Int.eq p_ct p_t = true.

Definition PIF (O:osabst) :=
  forall els tls ct p_ct mls pls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O curtid = Some (oscurt ct) ->
    OSAbstMod.get O absmutinfoid = Some (absmutinfo mls) ->
    OSAbstMod.get O absptlsid = Some (absptls pls) ->
    GET_ORP ct tls els p_ct ->
    HighestRdy tls ct ->
    IS_NOT_OWNER ct els ->
    forall t p_t,
      t <> ct ->
      TcbMod.get tls t <> None ->
      GET_ORP t tls els p_t ->
      ST_WAIT_T t els ->
      Int.ltu p_ct p_t = true \/ Int.eq p_ct p_t = true.

(*******init*******)
Definition eqdomTO:= fun (T:tasks) (O:osabst) =>
                       exists tls,
                         get O abtcblsid = Some (abstcblist tls) /\(
                           forall t, (exists a, get tls t = Some a ) ->  (exists C,get T t = Some C)  ).
Definition eqdomto:= fun (T:tasks) (O:osabst) =>
                       exists tls,
                         get O abtcblsid = Some (abstcblist tls) /\(
                           forall t, (exists a, get tls t = Some a ) <->  (exists C,get T t = Some C)  ).
Definition InitTasks (T:tasks) (p:progunit) (cst:clientst) (O:osabst) :=
  eqdomto T O /\ 
  forall t C,TasksMod.get T t = Some C -> 
  exists s f d1 d2 t, C = nilcont s /\ 
                      p f = Some (t, d1, d2, s).

Definition init_st O:=
  exists tls ptbl,
    OSAbstMod.get O absecblsid = Some (absecblist EcbMod.emp) /\
    OSAbstMod.get O absmutinfoid = Some (absmutinfo MibMod.emp) /\
    OSAbstMod.get O abstcblsid = Some (abstcblist tls) /\
    OSAbstMod.get O absptlsid = Some (absptls ptbl) /\
    forall t, exists p msg sus, TcbMod.get tls t = Some (p,rdy,msg,sus)
    .

Definition INIT (T:tasks) (p:progunit) (cst:clientst) (O:osabst) :=
InitTasks T p cst O /\ init_st O.

(**inv***)
Definition rdy_notin_wl tls els :=
  (forall t p m sus, TcbMod.get tls t = Some (p,rdy,m,sus) -> ~ ST_WAIT_T t els) /\
  (forall t p m eid tm sus, TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m,sus) -> IS_WAITING_E t eid els)/\
  (forall t eid,  IS_WAITING_E t eid els -> exists p tm m sus, TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m,sus)).

Definition not_in_two_wl els:= forall t,
                                 ~ exists eid eid', eid <> eid' /\ IS_WAITING_E t eid els /\ IS_WAITING_E t eid' els.

Definition owner_prio_prop tls els:=
  forall t p st m sus eid pe po l,
    TcbMod.get tls t = Some (p,st,m,sus) ->
    EcbMod.get els eid = Some (absmutexsem pe (Some (t,po)), l) ->
    (p = pe \/ p = po) /\ (Int.ltu pe po =true \/ Int.eq pe po =true).

Definition task_stat_prop tls:=
  forall t p st m sus,
    TcbMod.get tls t = Some (p,st,m,sus) ->
    st = rdy \/ (exists eid tm, st = wait (os_stat_mutexsem eid) tm).

Definition wait_prop tls els:=
  forall t p m eid tm sus,
    TcbMod.get tls t = Some (p,wait (os_stat_mutexsem eid) tm,m,sus) ->
    exists t' po m sus, IS_OWNER t' eid els /\ TcbMod.get tls t' = Some (po,rdy,m,sus) /\ (Int.ltu po p = true \/ Int.eq po p = true) /\
                    (forall op, GET_ORP t tls els op -> op = p).

Definition nowner_prio_prop tls els:=
  forall t p st m sus op,
    TcbMod.get tls t = Some (p,st,m,sus) ->
    IS_NOT_OWNER t els -> 
    GET_ORP t tls els op ->
    op = p.

Definition op_p_prop tls els :=
  forall t st p m sus op,
    TcbMod.get tls t = Some (p,st,m,sus) ->
    GET_ORP t tls els op ->
    Int.ltu p op = true \/ Int.eq p op = true.

Definition GOOD_DT O :=
  forall tls els mls ptbl,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    OSAbstMod.get O absmutinfoid = Some (absmutinfo mls) ->
    OSAbstMod.get O absptlsid = Some (absptls ptbl) ->
    rdy_notin_wl tls els /\
    owner_prio_prop tls els /\
    task_stat_prop tls/\
    wait_prop tls els/\
    op_p_prop tls els /\
    nowner_prio_prop tls els 
.

Definition GOOD_ST O :=
  UPIF O /\ GOOD_DT O.


(* Definition good_api_stmt s:= *)
(*   (exists vl, GoodMutexUnlock s vl) \/ *)
(*   (exists vl, GoodMutexLock s vl) \/ *)
(*   (exists vl, GoodMutexTimedlock s vl) \/ *)
(*   (exists vl, GoodMutexTrylock s vl) \/ *)
(*   (exists vl, GoodMutexInit s vl) \/ *)
(*   (exists vl, GoodMutexDestroy s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Init s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Destroy s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Settype s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Gettype s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Setprioceiling s vl) \/ *)
(*   (exists vl, GoodMutexAttr_Getprioceiling s vl) \/ *)
(*  s = ABORT. *)

Definition good_api_stmt s :=
  (exists vl, has_succ (mutexunlock vl) s) \/
    (exists vl, has_succ (mutexlock vl) s) \/
    (exists vl, has_succ (mutextimedlock vl) s) \/
    (exists vl, has_succ (mutextrylock vl) s) \/
    (exists vl, has_succ (mutex_init vl) s) \/
    (exists vl, has_succ (mutex_destroy vl) s) \/
    (exists vl, has_succ (mutexattrinit vl) s) \/
    (exists vl, has_succ (mutexattrdestroy vl) s) \/
    (exists vl, has_succ (mutexattrsettype vl) s) \/
    (exists vl, has_succ (mutexattrgettype vl) s) \/
    (exists vl, has_succ (mutexattrsetprioceiling vl) s) \/
    (exists vl, has_succ (mutexattrgetprioceiling vl) s) \/
    s = ABORT \/
    (exists vo, s = END vo).


Fixpoint GoodStmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sifthen _ _ => False
    | swhile _ s' => GoodStmt_h s'
    | sret => True
    | srete  _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => False
    | hapi_code _ => False
  end.

Fixpoint GoodStmt (s:stmts) (p:progunit) {struct s}:= 
  match s with
    | sskip v  => True
    | sassign e e' => True
    | sif e s1 s2 => GoodStmt s1 p/\ GoodStmt s2 p
    | sifthen e s => GoodStmt s p
    | swhile e s' => GoodStmt s' p
    | sret => True
    | srete e => True
    | scall f el =>  p f = None
    | scalle e f el => p f = None
    | sseq s1 s2 => GoodStmt s1 p /\ GoodStmt s2 p
    | sprint e => True
    | _ => False
  end. 

Fixpoint goodstmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sifthen _ s => goodstmt_h s
    | swhile _ s' => goodstmt_h s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => True
    | sfree _ _ => True
    | salloc _ _ => True
    | sprim _ => False
    | hapi_code s => good_api_stmt s
  end.

Definition goodeval_h (c:cureval):=
  match c with
    | cure _ => True
    | curs s => goodstmt_h s
  end.

Fixpoint goodks_h ks:=
  match ks with
    | kint _ _ _ _ => False
    | kevent c ke ks' => goodeval_h c /\ goodks_h ks'
    | kstop => True
    | kcall _ s _ ks' => goodks_h ks' /\ goodstmt_h s
    | kseq s ks' => goodks_h ks' /\ goodstmt_h s
    | kassignr _ _ ks' => goodks_h ks'
    | kassignl _ _ ks' => goodks_h ks'
    | kfuneval _ _ _ _ ks' => goodks_h ks'
    | kif s1 s2 ks' => goodks_h ks' /\ goodstmt_h s1 /\ goodstmt_h s2
    | kwhile _ s ks' => goodks_h ks' /\ goodstmt_h s
    | kret ks' => goodks_h ks'
  end.

Definition goodcode_h (c:code):=
  match c with
    | (c,(ke,ks)) => goodeval_h c /\ goodks_h ks
  end.

Definition goodtasks_h T:=
  forall t c, TasksMod.get T t = Some c -> goodcode_h c.

Definition NO_NEST_PENDING tls els:=
  forall t qid,
    TcbMod.get tls t <> None ->
    IS_OWNER t qid els ->
    (~ ST_WAIT_T t els /\ ~ exists qid', qid <> qid' /\ IS_OWNER t qid' els).

Definition NO_NEST_PENDING_O O:=
  forall els tls,
    OSAbstMod.get O absecblsid = Some (absecblist els) ->
    OSAbstMod.get O abtcblsid = Some (abstcblist tls) ->
    NO_NEST_PENDING tls els.

Definition hpstepok p T cst O T' cst' O':=
  hpstep p T cst O T' cst' O' /\
  (forall t c ke ks, get T' t = Some (c, (ke, ks)) -> 
                               c <> (curs (hapi_code spec_abort))).

Inductive hpstepstarok: hprog -> tasks -> clientst -> osabst  ->  
                      tasks -> clientst -> osabst  -> Prop:=
| hp_stepokO: forall (p:hprog) (T:tasks) (cst:clientst) O,
              hpstepstarok p T cst O  T cst O 
| hp_stepokS: forall p T T' T'' cst cst' cst'' O O' O'',
              hpstepok p T cst O T' cst' O' ->
              hpstepstarok p T' cst' O'  T'' cst'' O''->
              (forall t c ke ks, get T'' t = Some (c, (ke, ks)) -> 
                                           c <> (curs (hapi_code spec_abort))) ->
              hpstepstarok p T cst O T'' cst'' O'' .

Definition no_nest_client (client_code:progunit) O T cst:=
  forall  T' cst' O',
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    NO_NEST_PENDING_O O'.

Definition good_client_code client_code :=
      (forall (f : fid) (a : type) (b c : decllist) (s : stmts),
       client_code f = Some (a, b, c, s) -> GoodStmt_h s).

Definition no_abort T :=
    (forall t c ke ks, get T t = Some (c, (ke, ks)) -> 
                                           c <> (curs (hapi_code spec_abort))).

Definition no_abort_hpstep (client_code:progunit) O T cst:=
  forall  T' cst' O',
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    no_abort T'.

Definition INV_PROP (client_code:progunit) O T:=
  good_client_code client_code /\ 
  no_abort T /\
  GOOD_ST O.

(* Definition GOOD_API_CODE O T := *)
(*   exists C t, *)
(*     OSAbstMod.get O curtid = Some (oscurt t) /\ *)
(*     TasksMod.get T t = Some C /\ *)
(*     ( *)
(*       (*unlock*) *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexunlock_recvcnt_decrement_oweq (|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexunlock_get_ecb_ptr2(|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpost_nowt_return_prio_succ (|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpost_nowt_no_return_prio_succ (|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpost_exwt_return_prio_succ (|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpost_exwt_no_return_prio_succ (|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexunlock_after_post_errowner(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexunlock_after_post_errzero(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexunlock_after_post_errno(|vl|);;s)), (ke,ks)))\/ *)
(*       (*sched*) *)
(*       (exists ke ks s, C = (curs (hapi_code (sched;;s)), (ke,ks))) \/ *)
(*       (*lock*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexlock_type_recur_incre_one(|vl|))), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexlock_set_evloc_ptr(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpend_get_succ(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpend_block_no_lift(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpend_block_lift(|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks s, C = (curs (hapi_code ((ASSUME sc;; sched) ;; s)), (ke,ks))) \/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexpend_timeout_err_rdy(|vl|);;s)), (ke,ks))) \/ *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexlock_after_pend_succ_ecb(|vl|))), (ke,ks))) \/ *)
(*       (*timedlock*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutextimedlock_type_recur_incre_one(|vl|))), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutextimedlock_set_evloc_ptr(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutextimedlock_after_pend_succ_ecb(|vl|))), (ke,ks))) \/ *)
(*       (*trylock*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutextrylock_if_lt_cnt_max_yes(|vl|))), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutextrylock_get_ecb_ptr2(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexacc_succ(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutextrylock_after_acc_ptr(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutextrylock_after_acc_1(|vl|);;s)), (ke,ks)))\/ *)
(*       (*init*) *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_set1_init(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_set1_proc(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_set1_priocl(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_afterfor_set2_priocl(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_afterfor_set_protocol(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_afterfor_set_recursive(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_afterfor_set_cancel_safe(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexattr_init_afterfor_set_waitq_type(|vl|);; s1);; s2)), (ke,ks)))\/ *)

(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_placeholder(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexcre_seterr(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexcre_ecb_available(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s1 s2, C = (curs (hapi_code ( (mutexcre_ecb_activate(|vl|);; s1);; s2)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_ecb_ptr(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_cancel(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_protocol(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_recursive(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_owner(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_prioceiling(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_type(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutex_init_set_waitq(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutex_init_set_mux(|vl|))), (ke,ks)))\/ *)

(*       (*destroy*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutex_destroy_succ(|vl|))), (ke,ks)))\/ *)
(*       (*attrinit*) *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_set1_init(|vl|) ;; s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_set1_proc(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_set1_priocl(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_afterfor_set2_priocl(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_afterfor_set_protocol(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_afterfor_set_recursive(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_afterfor_set_cancel_safe(|vl|);;s)), (ke,ks)))\/ *)
(*       (exists ke ks vl s, C = (curs (hapi_code (mutexattr_init_afterfor_set_waitq_type(|vl|) ;; s)), (ke,ks)))\/ *)
(*       (*attrdestroy*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_destroy_clearinit(|vl|))), (ke,ks)))\/    *)
(*       (*attrsettype*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_settype_tp_neqdeflt_set_recv(|vl|))), (ke,ks)))\/ *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_settype_tp_eqdeflt_set_recv(|vl|))), (ke,ks)))\/ *)
(*       (*attrgettype*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_gettype_tp_set_recv(|vl|))), (ke,ks)))\/ *)
(*       (*attrsetprioceiling*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_setprioceiling_none_setpriocl(|vl|))), (ke,ks))) \/ *)
(*       (*attrgetprioceiling*) *)
(*       (exists ke ks vl, C = (curs (hapi_code (mutexattr_getprioceiling_tp_set_priocl(|vl|))), (ke,ks)))  *)
(*     ). *)


Ltac destruct_inverts1 H:=
  let Hx:= fresh in
  match type of H with
    | ?H1 \/ ?H2 => destruct H as [Hx | H]; [inverts Hx | destruct_inverts1 H]
    | exists _, _ = _ => let x:= fresh in (destruct H as (x&H);inverts H)
    | _ => idtac
  end.

