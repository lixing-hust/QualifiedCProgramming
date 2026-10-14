Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import ios_int.
Require Import int_lock.
Require Import evt_spec_defs.
Require Import ios_cap_defs.
Require Import part_pos_rgn_spec.

Definition PRIO_ERR := OS_PRIO_INVALID.
Definition PRIO_EXIST_ERR := OS_PRIO_EXIST.
Definition NO_TCB_ERR := OS_NO_MORE_TCB .
Definition NO_ERR := OS_NO_ERR.
Definition MAX_TCB := OS_MAX_TASKS.

Definition get_tls_len (tm:TcbMod.map) :=
  length (TcbMod.lst tm).

Definition get_els_len (tm:EcbMod.map) :=
  length (EcbMod.lst tm).

Definition DEL_IDLE_ERR := OS_TASK_DEL_IDLE.
Definition DEL_NO_EXIST_ERR := OS_TASK_DEL_ERR.
Definition SELF := OS_PRIO_SELF.

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.


Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.


Notation abtcblsid:=abstcblsid.

(* true cases: rdy \/ 
                        (wait x (Some Int.zero) /\
                              (x = os_stat_sem eid \/ x = os_stat_q eid \/
                               x = os_stat_mbox eid \/ x = os_stat_mutexsem eid)) *)
Definition in_rtbl (st:taskstatus):=
  match st with
    | rdy => True
    | wait x t_opt => match t_opt with
                                     | Some time => if Int.eq time Int.zero then True else False
                                     | None => False
                                  end
  end.

Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
 (exists tls prio st msg sus,
    get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio,st,msg,sus) /\ sus=false /\ in_rtbl st/\
    forall i prio' st' msg' sus',i <> t -> get tls i = Some (prio',st',msg',sus') -> sus'=false -> in_rtbl st'-> 
              Int.ltu prio prio'=true).

(* Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
 (exists tls prio st msg,
    get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio,st,msg) /\isrdy st/\
    forall i prio' st' msg',i <> t -> get tls i = Some (prio',st',msg') -> isrdy st'-> 
              Int.ltu prio prio'=true). *)

Definition nsc (O : osabst) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc).


Definition timedly_zero (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) => exists v,
       vl= ((Vint32 v)::nil) /\
       opv = None /\ v = Int.zero /\ O2=Some O1
  end.

Definition timedly_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      exists v,
      vl= ((Vint32 v)::nil) /\
      opv = None /\ Int.ltu Int.zero v=true/\
      exists tls p msg t sus,
         get O1 curtid = Some (oscurt t) /\ 
         get O1 abtcblsid = Some (abstcblist tls) /\  
        get tls t = Some (p,rdy,msg,false) /\
        O2=Some (set O1 abtcblsid (abstcblist (set tls t (p,wait os_stat_time (Some v),msg,sus))))
  end.
 
Definition timedly_nop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl= ((Vint32 v)::nil) /\
       (
         opv =  None /\ Int.ltu Int.zero v=true/\
         exists tls p st msg sus t,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
           get tls t = Some (p,st,msg,sus)/\
           ~ (st = rdy /\ sus = false) /\
           O2=Some O1        
       )
  end.

Definition timedly_idle  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl= ((Vint32 v)::nil) /\
       (
         opv =  None /\
         exists tls st msg t sus,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus)/\
           O2=Some O1        
       )
  end.

Definition tmdlycode (vl : vallist) :=
  timedly_zero (|vl|) ?? (timedly_succ  (|vl|) ;; isched ;; END None) ??
               timedly_nop (|vl|) ?? timedly_idle (|vl|).

Definition dlyapi:=(tmdlycode,(Tvoid,Tint16::nil)).


Definition timeget   (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        vl= nil/\
        (
          exists tm,
             get O1 ostmid = Some (ostm tm)/\
            opv =  (Some (Vint32 tm))/\
            O2 = Some O1
        )
  end.

Definition tmgetcode (vl : vallist):= timeget(|vl|).

Definition tmgetapi:=(tmgetcode,(Tint32,(nil:typelist))).


(*************************************************************************)
(*************************** abs op for events ****************************)
(*************************************************************************)

Definition TIME_OUT := OS_TIMEOUT.
Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) := 
  In t wl /\ 
  exists p st msg sus,
    get tls t = Some (p,st,msg,sus)/\
    forall t', t<>t' -> In t' wl -> exists p' st' msg' sus', get tls t' = Some (p',st',msg',sus') /\ (Int.ltu p p' = true)%Z.

Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2)
  | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2)
  | _ => s1 ;; s2
  end.

Local Open Scope code_scope. (* for notations such as sem_t to be recognized *) 
Local Open Scope int_scope. 

(* abs ops for internal functions for events *)

(* (****************************** sem acc ************************************) *)

Definition semacc_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v', 
      vl = (Vnull :: v' :: nil) /\
        opv = Some (Vint32 Int.zero) /\ 
        (v' = Vint32 Int.zero /\ O_opt = Some O1
         \/ v' <> Vint32 Int.zero /\ O_opt = None) 
  end.

Definition semacc_no_sem_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists sid v',
      vl = ((Vptr sid) :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 Int.zero) /\
            get O1 absecblsid = Some (absecblist els) /\
            (~ exists n wls, get els sid = Some (abssem n, wls)) /\
            (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
  end.

Definition semacc_no_source (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists sid v',
      vl = ((Vptr sid) :: v' :: nil) /\ 
        exists els,
          opv = (Some (Vint32 Int.zero)) /\
            get O1 absecblsid = Some (absecblist els) /\
            (exists wls, get els sid = Some (abssem Int.zero, wls)) /\
            (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
  end.

Definition semacc_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists sid v',
      vl = ((Vptr sid) :: v' :: nil) /\
        exists els n wls,
          opv = (Some (Vint32 n)) /\
            get O1 absecblsid = Some (absecblist els) /\
            get els sid = Some (abssem n, wls) /\
            Int.ltu Int.zero n = true /\
            (v' = Vint32 n /\ 
               O_opt = Some (set O1 absecblsid
                               (absecblist (set els sid (abssem (Int.sub n Int.one), wls))))
             \/ v' <> Vint32 n /\ O_opt = None)
  end.

Definition semacc (vl: vallist) :=
    semacc_null (|vl|)
      ?? semacc_no_sem_err (|vl|)
      ?? semacc_no_source (|vl|)
      ?? semacc_succ (|vl|).


(* (**************************** sem cre ******************************************) *)

Definition semcre_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists rv,
        vl = ( rv :: nil) /\
        opv = Some Vnull /\
        ((rv = Vnull /\ O_opt = Some O1)   \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition semcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists n v' locmp locmp' t,
        vl = ((Vint32 n) :: v' :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        opv = Some Vnull /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\ 
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre1)) /\  
        (v'= Vnull /\ O_opt = Some (set O1 evlocid (evloc locmp'))  \/ v' <> Vnull /\ O_opt = None) 
  end.

Definition tsk_normal_ev locmp ptrmp tid sid :=
  get locmp tid = Some (Vint32 (Int.repr __EvLoc_normal)) /\
  (exists muxp semp qp, 
      get ptrmp tid = Some (muxp, semp, qp) /\
      (muxp = Vptr sid \/ semp = Vptr sid \/ qp = Vptr sid)).  

Definition semcre_ecb_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists v' sls sid t locmp locmp' ptrmp ptrmp',
    exists muxp semp qp,
        vl = (v' :: nil) /\
        opv = None /\
        get O1 absecblsid = Some (absecblist sls) /\
        get sls sid = None /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (muxp, semp, qp) /\
        ptrmp' = set ptrmp t (muxp, Vptr sid, qp) /\
        (v' = Vptr sid /\ O_opt = Some (set (set O1 evlocid (evloc locmp')) evptrid (evptr ptrmp'))
         \/ v' <> Vptr sid /\ O_opt = None 
         \/ (exists t', tsk_normal_ev locmp ptrmp t' sid) /\ O_opt = None)
          (* the last disjunct reflects the assumption that no event is used while being created *)
  end. 

Definition semcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists n sid sls t locmp locmp' O',
      vl = ((Vint32 n) :: (Vptr sid) :: nil) /\
      (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
      opv = Some (Vptr sid) /\
      get O1 absecblsid = Some (absecblist sls) /\
      get sls sid = None /\
      get O1 evlocid = Some (evloc locmp) /\
      get O1 curtid = Some (oscurt t) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
      O' = (set O1 absecblsid (absecblist (set sls sid (abssem n, nil)))) /\
      O_opt = Some (set O' evlocid (evloc locmp'))
  end.

Definition semcre (vl: vallist) :=
  match vl with
    vn :: v' :: nil => 
    semcre_iserr (| v' ::nil |) ??
    semcre_no_free (| vn :: v' :: nil |) ??
    (semcre_ecb_available (| v' :: nil |) ;; semcre_ecb_activate (| vn :: v' :: nil |))
  | _ => ABORT 
  end. 


(* (************************************ sem_pend *************************************) *)

Definition sem_pend_null_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     exists v k,
       vl = (Vnull :: v  :: k :: nil) /\
       opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL) ) /\
      (k = Vint32 (Int.repr OS_ERR_PEVENT_NULL)  /\ O_opt = Some O1
      \/ k <>  Vint32 (Int.repr OS_ERR_PEVENT_NULL)  /\ O_opt = None)
  end.

Definition sem_pend_no_active_evt_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists qid v k,
    vl = ((Vptr qid) :: v :: k :: nil)/\
    exists els,
      get O1 absecblsid = Some (absecblist els) /\
      get els qid = None /\
      opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
      (k = Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = Some O1 \/
       k <> Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = None)
  end.  

Definition sem_pend_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) => 
   exists qid v k,
   vl= ((Vptr qid) :: (Vint32 v) :: k :: nil)/\
   (
     exists els,
       get O1 absecblsid = Some (absecblist els) /\
       (exists d, get els qid = Some d /\ (~exists x wls, d = (abssem x, wls)) )/\
       opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE) ) /\
       (k = Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = Some O1
        \/ k <>  Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = None)
   )
  end.

Definition sem_pend_from_idle_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
  | (rv, O_opt) =>
    (
      exists qid v k,
        vl=(Vptr qid::Vint32 v :: k :: nil) /\
        exists tls st msg t sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (Int.repr OS_IDLE_PRIO, st, msg, sus) /\ 
          rv = None /\
          O_opt = None
    )
  end.

Definition sem_pend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
  | (rv, O_opt) =>
    (
      exists qid v k,
        vl = (Vptr qid :: Vint32 v ::k ::nil) /\
        exists tls st msg prio t sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (prio,st,msg,sus) /\
          ~ (st = rdy /\ sus = false) /\
          rv = None /\ 
          O_opt = None
    )
  end.

Definition sem_pend_inst_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  |  (opv, O_opt) =>
     (exists qid v k,
         vl = ((Vptr qid) :: Vint32 v :: k :: nil) /\ 
         exists els n wls,
           get O1 absecblsid = Some (absecblist els) /\
           Int.ltu Int.zero n = true /\
           get els qid = Some (abssem n, wls) /\
           opv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
           (k = Vint32 (Int.repr OS_NO_ERR)  
            /\ O_opt = Some (set O1 absecblsid
                                 (absecblist (set els qid (abssem (Int.sub n Int.one), wls))))
            \/ k <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
     )
  end.

Definition sem_pend_block (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
    (
      (
        exists qid v m k,
          vl = (Vptr qid :: Vint32 v :: k :: nil) /\
          exists tls tls' qls qls' wl p st t sus t_opt,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist qls) /\
            get O1 abstcblsid = Some (abstcblist tls) /\ 
            get qls qid = Some (abssem Int.zero, wl) /\
            qls'=set qls qid (abssem Int.zero, t::wl)/\
            get tls t = Some (p,st,m,sus) /\
            tls' = set tls t (p,wait (os_stat_sem qid) t_opt,m,sus)/\
            ((t_opt = Some v /\ v <> Int.zero) \/ (t_opt = None /\ v = Int.zero)) /\
            O_opt = Some (set ( set O1 abstcblsid (abstcblist tls') ) 
                              absecblsid (absecblist qls')) /\
            opv = None
      )
    )
  end.

Definition sem_pend_after_sched (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (rv, O_opt) =>
    exists qid v k,
    vl = (Vptr qid :: Vint32 v :: k :: nil) /\
    (
      exists tls p st t m sus,
        get O1 curtid = Some (oscurt t) /\
        get O1 abstcblsid = Some (abstcblist tls)/\
        get tls t =Some (p, st, m, sus)/\
        rv = None /\
        ((((st = rdy /\ sus = false)
           \/ (st = wait (os_stat_sem qid) ( Some Int.zero ) /\ sus = false))  /\ O_opt = Some O1)
         \/ ( ~((st = rdy /\ sus = false) \/ (st = wait (os_stat_sem qid) (Some Int.zero) /\ sus = false)) /\ O_opt = None)) 
    )
  end.

Definition sem_pend_timeout_err_rdy (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (rv, O_opt) =>
   exists qid v k,
   vl = (Vptr qid :: Vint32 v :: k :: nil) /\
   (
     (
       exists tls p t m sus els els' n wl,
         get O1 curtid = Some (oscurt t) /\
         get O1 abstcblsid = Some (abstcblist tls)/\
         get tls t =Some (p, wait (os_stat_sem qid) (Some Int.zero), m, sus)/\
         get O1 absecblsid = Some (absecblist els) /\
         get els qid = Some (abssem n, wl) /\
         In t wl /\
         els' = set els qid (abssem n, (remove_tid t wl)) /\
         rv = Some (Vint32 (Int.repr OS_TIMEOUT) ) /\
         (k = Vint32 (Int.repr OS_TIMEOUT)  /\
          O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (p, rdy,m,false)))) 
                            absecblsid (absecblist els'))
          \/ k <>  Vint32 (Int.repr OS_TIMEOUT)  /\ O_opt = None)
     )
   )
  end.

Definition sem_pend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (rv, O_opt) =>
   exists qid v k,
   vl= (Vptr qid :: Vint32 v :: k :: nil) /\
   (
     exists tls t p st m sus,
       get O1 curtid = Some (oscurt t) /\
       get O1 abstcblsid = Some (abstcblist tls)/\
       get tls t = Some (p, st, m, sus) /\
       ~(exists wt, st = wait (os_stat_sem qid) wt) /\
       rv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
       (k = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some O1
        \/ k <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
   )
  end.

Definition sem_pend  (vl: vallist):=
  sem_pend_null_err (|vl|)
  ?? sem_pend_no_active_evt_err (|vl|) 
  ?? sem_pend_wrong_type_err (|vl|)
  ?? sem_pend_from_idle_err (|vl|)
  ?? sem_pend_not_ready_err (|vl|)
  ?? sem_pend_inst_get_succ (|vl|)
  ?? (sem_pend_block (|vl|) ;; isched ;;
      sem_pend_after_sched (|vl|) ;;
      (sem_pend_timeout_err_rdy (|vl|) ?? sem_pend_block_get_succ (|vl|))).  


(* (*************************************** sem post **************************************) *)

Definition sem_post_null_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
        exists v', 
        vl = (Vnull :: v' :: nil) /\
          opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
          (v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ O2 = Some O1 \/
             v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ O2 = None)  
  end.

Definition sem_post_no_active_evt_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists qid v',
    vl = ((Vptr qid) :: v' :: nil) /\ 
    exists els,
      get O1 absecblsid = Some (absecblist els) /\
      get els qid = None /\
      opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
      (v' = (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = Some O1 \/ 
       v' <> (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = None) 
  end.

(* assumes that the gjb semaphore corresponding to the current ECB is not a binary semaphore *) 
Definition sem_post_assumes_not_bin (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) =>
    exists qid,
    vl = ((Vptr qid) :: nil) /\
    exists semifo,
      get O1 seminfoid = Some (seminfo semifo) /\
      exists posv sc,
        get semifo posv = Some (infotid qid, Int.one, sc) /\ O2 = None
  end.

Definition sem_post_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v', 
      vl= ((Vptr qid) :: v' :: nil) /\ 
        exists els,
          get O1 absecblsid = Some (absecblist els) /\
            (exists d, get els qid = Some d /\ (~exists n wls, d = (abssem n, wls))) /\  
            opv = (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE))) /\ 
            (v' = (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O2 = Some O1 \/
               v' <> (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O2 = None) 
  end.

Definition sem_post_ovf_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O2) =>
      exists sid v',
      vl=  (Vptr sid :: v' :: nil) /\
        exists sls n wl,
          get O1 absecblsid = Some (absecblist sls) /\
            get sls sid = Some (abssem n,wl) /\
            (Int.ltu n (Int.repr 65535) = false) /\
            opv = (Some (Vint32 (Int.repr OS_SEM_OVF))) /\
            (v' = (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = Some O1 \/
               v' <> (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = None) 
  end.

Definition sem_post_ex_wt_succ (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v' sus,
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls t' wl p st m n tls' els', 
          get O1 abtcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            (GetHWait tls wl t') /\
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            get tls t' = Some (p, st, m, sus) /\
            v' = (Vint32 (Int.repr OS_NO_ERR)) /\
            tls' = set tls t' (p, rdy, Vnull, sus) /\ 
            els' = set els qid (abssem n, (remove_tid t' wl)) /\
            O2 = Some (set (set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els'))
  end.

Definition sem_post_ex_wt_abt (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls wl n, 
          get O1 abtcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            v' <> (Vint32 (Int.repr OS_NO_ERR)) /\
            O2 = None
  end.

Definition sem_post_put_sem_in_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els n wls,
          get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wls)) /\
            Int.ltu n (Int.repr 65535) = true /\
            opv = (Some (Vint32 (Int.repr OS_NO_ERR ))) /\
            (v' = (Vint32 (Int.repr OS_NO_ERR)) /\ 
               O2 = Some(set O1 absecblsid (absecblist (set els qid (abssem (Int.add n Int.one), wls)))) \/
               v' <> (Vint32 (Int.repr OS_NO_ERR )) /\ O2 = None) 
  end.

Definition sem_post (vl: vallist) :=
  match vl with
    v1 :: v2 :: nil => 
      sem_post_null_err (|vl|)
        ?? sem_post_no_active_evt_err (|vl|)  
        ?? sem_post_wrong_type_err (|vl|)
        ?? sem_post_ovf_err (|vl|)
        ?? ((sem_post_ex_wt_succ (|vl|) ?? sem_post_ex_wt_abt (|vl|));; 
            isched ;;
            END (Some (Vint32 (Int.repr OS_NO_ERR)))) 
        ?? (sem_post_assumes_not_bin (|v1::nil|) ?? sem_post_put_sem_in_succ (|vl|))
  | _ => spec_abort 
  end.


(* (*************************************** sem post bin **************************************) *)

Definition sem_post_bin_ovf_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O2) =>
      exists sid v',
      vl=  (Vptr sid :: v' :: nil) /\
        exists sls n wl,
          get O1 absecblsid = Some (absecblist sls) /\
            get sls sid = Some (abssem n,wl) /\
            (Int.ltu n (Int.repr 1) = false) /\
            opv = (Some (Vint32 (Int.repr OS_SEM_OVF))) /\
            (v' = (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = Some O1 \/
               v' <> (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = None) 
  end.

Definition sem_post_bin (vl: vallist) :=
  match vl with
    v1 :: vl' =>
      match vl' with
        v2 :: nil =>
          sem_post_null_err (|vl|)
            ?? sem_post_no_active_evt_err (|vl|)  
            ?? sem_post_wrong_type_err (|vl|)
            ?? sem_post_bin_ovf_err (|vl|)
            ?? ((sem_post_ex_wt_succ (|vl|) ?? sem_post_ex_wt_abt (|vl|));; 
                isched ;;
                END (Some (Vint32 (Int.repr OS_NO_ERR)))) 
            ?? sem_post_put_sem_in_succ (|vl|)
        | _ => spec_abort 
      end                 
  | _ => spec_abort 
  end.

(* (*************************************** sem post ipc **************************************) *)

Definition sem_post_ipc (vl: vallist) :=
  match vl with
    v1 :: v2 :: nil =>
          sem_post_null_err (|vl|)
            ?? sem_post_no_active_evt_err (|vl|)  
            ?? sem_post_wrong_type_err (|vl|)
            ?? sem_post_ovf_err (|vl|)
            ?? ((sem_post_ex_wt_succ (|vl|) ?? sem_post_ex_wt_abt (|vl|));;
                END (Some (Vint32 (Int.repr OS_NO_ERR)))) 
            ?? sem_post_put_sem_in_succ (|vl|)
  | _ => spec_abort 
  end.


(* (************************************ mutex acc *************************************) *)

Definition mutexacc_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v rv,
        vl = ( v :: rv :: nil) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\ O_opt = Some O1)   \/ rv <> (Vint32 Int.zero) /\ O_opt = None) 
  end.

Definition mutexacc_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v', 
      vl = (Vnull (* :: (Vptr err) *) :: v' :: nil) /\
        opv = Some (Vint32 Int.zero) /\ 
        (v' = Vint32 Int.zero /\ O_opt = Some O1
         \/ v' <> Vint32 Int.zero /\ O_opt = None) 
  end.

Definition mutexacc_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid v',
      vl = ((Vptr mid) (* :: (Vptr err) *) :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 Int.zero) /\
            get O1 absecblsid = Some (absecblist els) /\
           ~(exists x y wls, get els mid = Some (absmutexsem x y,wls)) /\
            (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
  end.

Definition mutexacc_no_available  (vl: vallist) (O1 : osabst) (rst : option val *option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v' ,
       vl= ((Vptr mid) (* :: (Vptr err) *) :: v' :: nil)/\
       (
           exists qls, 
              opv =  (Some (Vint32 Int.zero))/\
              get O1 absecblsid = Some (absecblist qls) /\
             (exists wls p o,get qls mid =Some (absmutexsem p (Some o),wls))/\
             (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
         )
     )
  end.

Definition mutexacc_pip_hold  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v',
       vl= ((Vptr mid) (* :: (Vptr err) *) :: v' :: nil)/\
       (
         exists qls tls p wl pt st m sus t,
             get O1 curtid = Some (oscurt t) /\
             opv =  None /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (pt,st,m,sus) /\
             get qls mid =Some (absmutexsem p None, wl)/\
            ( Int.ltu p pt = true /\ O_opt = Some O1
             \/ Int.ltu p pt = false /\ O_opt = None)
       )
     )
  end.

Definition mutexacc_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v',
       vl= ((Vptr mid) (* :: (Vptr err)  *):: v' :: nil)/\
       (
         exists qls tls p wl pt st m sus t,
             get O1 curtid = Some (oscurt t) /\
             opv =  (Some (Vint32 Int.one))/\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (pt,st,m,sus) /\
             Int.ltu p pt = true /\
             get qls mid =Some (absmutexsem p None, wl)/\
            (v' = (Vint32 Int.one) /\ 
               O_opt = Some (set O1 absecblsid (absecblist (set qls mid (absmutexsem p (Some (t,pt)),wl))))
             \/ v' <> (Vint32 Int.one) /\ O_opt = None)
       )
     )
  end.

Definition mutexacc (vl: vallist) :=
    mutexacc_iserr (|vl|) 
    ?? mutexacc_null (|vl|)
    ?? mutexacc_wrong_type_err (|vl|)
    ?? mutexacc_no_available (|vl|)
    ?? (mutexacc_pip_hold (|vl|) ;; mutexacc_succ (|vl|)).


(* (*************************************** mutex cre **************************************) *) 

Definition prio_available prio tls:=
  forall t p x y sus, get tls t = Some (p, x, y, sus) -> Int.eq prio p = false.

Definition mutexcre_err_valid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        ((exists errid ed, verr = Vptr errid /\  get ebls errid = Some ed /\ O_opt = Some O1)  
          \/ ((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutexcre_err_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        (((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutexcre_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists rv,
        vl = ( rv :: nil) /\
        opv = Some Vnull /\
        ((rv = Vnull /\ O_opt = Some O1)   \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_seterr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists errid ebls ebls' erv,
        vl = ((Vptr errid) :: (Vint32 erv) :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        (exists ed, get ebls errid = Some ed) /\
        ebls' = EbMod.set ebls errid erv /\
        opv = None /\
        O_opt = Some (set O1 eblsid (eblist ebls'))
  end.

Definition mutexcre_prio_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio rv,
        vl = ((Vint32 prio) :: rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = false /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1 \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_prio_not_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio rv ptls d,
        vl = ((Vint32 prio) ::  rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some d /\
        d <> Null /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1  \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio  rv ptls,
        vl = ((Vint32 prio) ::  rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some Null /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1 \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_ecb_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists prio rv ptls ptls' els eid t locmp locmp',
    exists ptrmp ptrmp' muxp semp qp,
        vl = ((Vint32 prio) :: rv :: nil) /\
        opv = None /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some Null /\
        ptls' = PtbMod.set ptls prio Holder /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = None /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (muxp, semp, qp) /\
        ptrmp' = set ptrmp t (Vptr eid, semp, qp) /\
        (rv = Vptr eid /\ 
          O_opt = Some (set (set (set O1 absptlsid (absptls ptls')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
         \/ rv <> Vptr eid /\ O_opt = None 
         \/ (exists t', tsk_normal_ev locmp ptrmp t' eid) /\ O_opt = None)
          (* the last disjunct reflects the assumption that no event is used while being created *)
  end. 

Definition mutexcre_prio_vhold (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio ptls d,
        vl = ((Vint32 prio) :: nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some d /\
        opv = None /\
        (d = Holder /\ O_opt = Some O1  \/ d <> Holder /\ O_opt = None) 
  end.

Definition mutexcre_prio_unused (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio els,
        vl = ((Vint32 prio) :: nil) /\
         get O1 absecblsid = Some (absecblist els) /\
        opv = None /\
        (~(exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) /\ O_opt = Some O1
           \/ (exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) /\ O_opt = None) 
  end.

Definition mutexcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists prio eid els t locmp locmp' O',
      vl = ((Vint32 prio) :: (Vptr eid) :: nil) /\
      Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
      opv = Some (Vptr eid) /\
      get O1 absecblsid = Some (absecblist els) /\
      get els eid = None /\
      get O1 evlocid = Some (evloc locmp) /\
      get O1 curtid = Some (oscurt t) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
      O' = (set O1 absecblsid (absecblist (set els eid (absmutexsem prio None, nil)))) /\
      O_opt = Some (set O' evlocid (evloc locmp'))
  end.

Definition mutexcre (vl: vallist) :=
  match vl with
    vp :: verr :: rv :: nil => 
    (mutexcre_iserr (| rv :: nil |) ;;
           (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_CREATE_ISR)) :: nil |))) ??
    (mutexcre_prio_err (| vp :: rv :: nil |) ;;
           (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_INVALID)) :: nil |))) ??
    (mutexcre_prio_not_available (| vp :: rv :: nil |) ;;
            (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_EXIST)) :: nil |))) ??
    (mutexcre_no_free (| vp :: rv :: nil |) ;;
            (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) :: nil |))) ??
    (mutexcre_ecb_available  (| vp :: rv :: nil |) ;; 
      mutexcre_prio_vhold (| vp :: nil |);; mutexcre_prio_unused (| vp :: nil |) ;;
      mutexcre_ecb_activate  (| vp :: rv :: nil |) ;;
             (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_NO_ERR)) :: nil |)))
  | _ => ABORT 
  end.


(* (************************************* mutex pend **************************************) *)

Definition mutexpend_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vt v', 
      vl = (Vnull  :: vt :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ 
        (v' = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None) 
  end.

Definition mutexpend_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid vt v',
      vl = ((Vptr mid) :: vt :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
            get O1 absecblsid = Some (absecblist els) /\
            ~(exists x y wls, get els mid = Some (absmutexsem x y,wls)) /\
            (v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1
             \/ v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.

Definition mutexpend_idle_err(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl= (Vptr mid :: vt :: v' :: nil) /\
         exists tls st msg sus t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     (
       exists mid vt v',
         vl=(Vptr mid :: vt :: v' ::nil) /\
         exists tls st msg sus prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg,sus) /\
           ~ (st = rdy /\ sus = false) /\
           opv = None /\ 
           O_opt = None
     )
  end.

Definition mutexpend_curp_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls st msg sus prio t p o wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p o,wl) /\
           get tls t = Some (prio,st,msg,sus) /\
           Int.ltu p prio = false /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_get_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
         exists mid vt v',
           vl= (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio st m sus p t,
         get O1 curtid = Some (oscurt t) /\
         get O1 absecblsid = Some (absecblist els) /\
         get O1 abstcblsid = Some (abstcblist tls) /\
         get els mid = Some (absmutexsem p None,nil) /\
         get tls t = Some (prio,st,m,sus)/\
         Int.ltu p prio = true /\
         opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
         (v' = Vint32 (Int.repr OS_NO_ERR) /\
           O_opt = Some (set O1 absecblsid (absecblist (set els mid (absmutexsem p (Some (t,prio)),nil))))
         \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
     )
  end.

Definition mutexpend_curp_eq_owner_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio t p wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p (Some(t, prio)),wl) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_owner_idle_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio ot p wl ost om sus,
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p (Some(ot, prio)),wl) /\
           get tls ot = Some (Int.repr OS_IDLE_PRIO, ost, om, sus) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_owner_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     (
       exists mid vt v',
         vl=(Vptr mid :: vt :: v' ::nil) /\
         exists els tls st msg sus pip prio ot wl opt,
             get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
           get tls ot = Some (opt,st,msg,sus) /\
           ~ (st = rdy /\ sus = false) /\
           opv = None /\ 
           O_opt = None
     )
  end.

Definition mutexpend_block_lift  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       (
         exists mid vt v' t_opt,
           vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
           exists tls tls' tls'' els els' wl pip ot prio,
             exists  cpt  opt ct cst ost cm om ptls ptls',
              exists sus sus',
                get O1 curtid = Some (oscurt ct) /\
                  get O1 absecblsid = Some (absecblist els) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                  get O1 absptlsid = Some (absptls ptls) /\
                 
                 get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
                 get tls ct = Some (cpt, cst, cm, sus) /\
                 get tls ot = Some (opt, ost, om, sus') /\

                 Int.eq opt pip = false /\
                 Int.ltu cpt prio = true /\
                 ((t_opt = Some vt /\ vt <> Int.zero) \/ (t_opt = None /\ vt = Int.zero)) /\
                 ptls' = set (set ptls opt (Holder)) pip (Valid_Addr ot) /\
                 els' = set els mid (absmutexsem pip (Some (ot,prio)), ct::wl) /\
                 tls' = set tls ct (cpt,wait (os_stat_mutexsem mid) t_opt, cm, sus) /\
                 tls'' = set tls' ot (pip, ost, om, sus') /\
                 O_opt = Some (set (set (set O1 abtcblsid (abstcblist tls'')) absecblsid (absecblist els')) absptlsid
                                                         (absptls ptls')) /\
                 opv = None
         )
     )
  end.

Definition mutexpend_block_no_lift  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       (
         exists mid vt v' t_opt,
           vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
           exists tls tls' els els' wl pip ot prio,
             exists  cpt  opt ct cst ost cm om,
              exists sus sus',
                get O1 curtid = Some (oscurt ct) /\
                  get O1 absecblsid = Some (absecblist els) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                 
                 get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
                 get tls ct = Some (cpt, cst, cm, sus) /\
                 get tls ot = Some (opt, ost, om, sus') /\

                 ~(Int.eq opt pip = false /\ Int.ltu cpt prio = true) /\
                 ((t_opt = Some vt /\ vt <> Int.zero) \/ (t_opt = None /\ vt = Int.zero)) /\
                 els' = set els mid (absmutexsem pip (Some (ot,prio)), ct::wl) /\
                 tls' = set tls ct (cpt,wait (os_stat_mutexsem mid) t_opt, cm, sus) /\
                 O_opt = Some (set (set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els')) /\
                 opv = None
         )
     )
  end.

Definition mutexpend_after_sched (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl=(Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         (
           exists tls p st t m sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, st, m, sus)/\
              opv = None /\
              ((((st = rdy /\ sus = false)
                 \/ (st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false))  /\ O_opt = Some O1)
              \/ ( ~((st = rdy /\ sus = false) \/ 
                             (st = wait (os_stat_mutexsem mid) (Some Int.zero) /\ sus = false))  /\ O_opt = None))
         )
       )
  end.

Definition mutexpend_timeout_err_rdy (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl=(Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         (
           exists tls p t m sus els els' pip o wl,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, wait (os_stat_mutexsem mid) (Some Int.zero), m, sus)/\
             get O1 absecblsid = Some (absecblist els) /\
              get els mid = Some (absmutexsem pip o,wl) /\
              In t wl /\
              els' = set els mid (absmutexsem pip o, (remove_tid t wl)) /\
              opv = Some (Vint32 (Int.repr OS_TIMEOUT) ) /\
              (v' = Vint32 (Int.repr OS_TIMEOUT)  /\
                O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (p, rdy, m, false)))) 
                                                        absecblsid (absecblist els'))
              \/ v' <>  Vint32 (Int.repr OS_TIMEOUT)  /\ O_opt = None)
         )
       )
  end.

Definition mutexpend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         exists tls t p st m sus,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls)/\
            get tls t = Some (p, st, m, sus) /\
            ~(exists wt, st = wait (os_stat_mutexsem mid) wt) /\
           opv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
          (v' = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some O1
              \/ v' <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
       )
  end.

Definition mutexpend (vl:vallist):=
  mutexpend_null (|vl|) ??
  mutexpend_type_err (|vl|) ??
  mutexpend_idle_err (|vl|) ??
  mutexpend_not_ready_err (|vl|) ??
  mutexpend_curp_err (|vl|) ??
  mutexpend_get_succ (|vl|) ??
  mutexpend_curp_eq_owner_err (|vl|) ??
  mutexpend_owner_idle_err (| vl |) ??
  (( (mutexpend_owner_not_ready_err (| vl |) ??
         mutexpend_block_lift (|vl|)) ??
        mutexpend_block_no_lift (|vl|)) ;; 
     isched ;; mutexpend_after_sched (|vl|) ;;
        (mutexpend_timeout_err_rdy (|vl|) ?? mutexpend_block_get_succ (|vl|) )).


(* (************************************ mutex post **************************************) *)

Definition mutexpost_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v rv,
        vl = ( v :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_POST_ISR)) /\
        ((rv = (Vint32 (Int.repr OS_ERR_POST_ISR)) /\ O_opt = Some O1)   \/ rv <> (Vint32 (Int.repr OS_ERR_POST_ISR)) /\ O_opt = None) 
  end.

Definition mutexpost_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v', 
      vl = (Vnull  :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ 
        (v' = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None) 
  end.

Definition mutexpost_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid v',
      vl = ((Vptr mid) :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
            get O1 absecblsid = Some (absecblist els) /\
            ~(exists x y wls, get els mid = Some (absmutexsem x y,wls)) /\
            (v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1
             \/ v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.

Definition mutexpost_owner_hold (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' tls,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr o ptls,
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
              get O1 absptlsid = Some (absptls ptls) /\
     
             get els mid = Some (absmutexsem pr o,wl) /\
             opv =  None /\
              ( ((o = None ) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy, m, false) 
                                                        /\ (prio = op
                                                              \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder )
                                                                     /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) ))))) 
                  /\ O_opt = Some O1 
             \/
             ~((o = None) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy,m,false)
                                                            /\ (prio = op
                                                                  \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder)
                                                                         /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) ))))) /\
              O_opt = None)
  end.

Definition mutexpost_no_owner_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' t tls,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = Some (absmutexsem pr None,wl) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER)))/\
            (v' = Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = Some O1
             \/ (v' <> Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = None))
  end.

Definition mutexpost_not_owner_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' t tls ot op,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr prio st m sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = Some (absmutexsem pr (Some (ot,op)),wl) /\
             get tls ot = Some (prio, st, m, sus) /\
             (prio = pr \/ prio = op) /\
             t <> ot /\ 
             opv =  (Some (Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER)))/\
            (v' = Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = Some O1
             \/ (v' <> Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = None))
  end.

Definition mutexpost_nowt_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v',
       vl= (Vptr mid :: v' :: nil) /\
       (
         (
           exists els tls els' tls' pip p' st m t ptls,
              exists ptls' sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist els) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\
             get els mid = Some (absmutexsem pip (Some (t,p')),nil) /\
             get tls t = Some (pip,st,m,sus) /\
             tls' = set tls t (p',st,m,sus) /\
             els' = set els mid (absmutexsem pip None,nil) /\
             ptls' = set (set ptls p' (Valid_Addr t)) pip Holder /\
             opv = (Some (Vint32 (Int.repr OS_NO_ERR)))/\
             (v' = Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = Some (set (set ( set O1 abstcblsid (abstcblist tls') ) absecblsid (absecblist els')) absptlsid (absptls ptls') )
              \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition mutexpost_nowt_no_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid v' ptls ptls',
       vl= (Vptr qid :: v' :: nil) /\
           exists qls tls qls' pip op pt st m sus t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\
             get qls qid = Some (absmutexsem pip (Some (t,op)),nil) /\
             get tls t = Some (pt,st,m,sus) /\
             Int.eq pt pip = false /\
             qls' = set qls qid (absmutexsem pip None,nil) /\
             ptls' = set ptls pip Holder /\
             opv =(Some (Vint32 (Int.repr OS_NO_ERR)))/\
             (v' = Vint32 (Int.repr OS_NO_ERR) /\  O_opt = Some (set (set O1 absecblsid (absecblist qls')) absptlsid (absptls ptls'))
              \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
  end.

Definition mutexpost_wl_highest_prio_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
      vl= (Vptr qid :: v' :: nil) /\
      (
        (
          exists els tls pip t pt wl t' pw st m,
            exists sus,
               get O1 absecblsid = Some (absecblist els) /\
               get O1 abstcblsid = Some (abstcblist tls) /\
              get els qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
              wl <> nil /\
              GetHWait tls wl t'/\ 
              get tls t' = Some (pw,st,m,sus) /\
              opv = None /\
              Int.ltu pip pw = false /\ O_opt = None
        )
      )
  end.

Definition mutexpost_exwt_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
      vl= (Vptr qid :: v' :: nil) /\
      (
        (
          exists qls tls qls' tls' tls'' ptls ptls',
            exists pip p' pt st m wl t' st' m' t ,
              exists sus sus',
               get O1 curtid = Some (oscurt t) /\
               get O1 absecblsid = Some (absecblist qls) /\
               get O1 abstcblsid = Some (abstcblist tls) /\
               get O1 absptlsid = Some (absptls ptls) /\
              get qls qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
              wl <> nil /\
              GetHWait tls wl t'/\ 
              get tls t = Some (pip,st,m,sus) /\
              get tls t' = Some (p',st',m',sus') /\
              ptls' = set (set ptls pt (Valid_Addr t)) pip Holder /\
              tls' = set tls t (pt,st,m,sus) /\
              tls''= set tls' t' (p',rdy,Vnull,sus')/\
              qls' = set qls qid (absmutexsem pip (Some (t',p')),remove_tid t' wl) /\
              
              opv = None /\
              ( v' = Vint32 (Int.repr OS_NO_ERR)  /\ 
                    O_opt = Some (set (set ( set O1 abtcblsid (abstcblist tls'') ) absecblsid (absecblist qls')) absptlsid (absptls ptls'))
                \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
        )
      )
  end.

Definition mutexpost_exwt_no_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
       vl= (Vptr qid :: v' :: nil) /\
       (
         (
           exists qls tls qls' tls' t ptls ptls',
             exists pip p' p'' pt st m wl t' st' m' ,
              exists sus sus',
               get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\

             get qls qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
             wl <> nil /\
             GetHWait tls wl t'/\
             Int.eq p'' pip = false /\
             get tls t = Some (p'',st,m,sus) /\
             get tls t' = Some (p',st',m',sus') /\
             
             tls'= set tls t' (p',rdy,Vnull,sus')/\
             qls' = set qls qid (absmutexsem pip (Some (t',p')),remove_tid t' wl) /\
             ptls' = set ptls pip Holder /\

             opv = None /\
             ( v' = Vint32 (Int.repr OS_NO_ERR)  /\ 
                    O_opt = Some (set (set ( set O1 abtcblsid (abstcblist tls') ) absecblsid (absecblist qls')) absptlsid (absptls ptls'))
               \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None )
         )
       )
  end.

Definition mutexpost_aft_owner (vl:vallist):=
  mutexpost_no_owner_err (|vl|) ??
  mutexpost_not_owner_err (|vl|) ??
  mutexpost_nowt_return_prio_succ (|vl|) ??
  mutexpost_nowt_no_return_prio_succ (|vl|) ?? 
  mutexpost_wl_highest_prio_err (|vl|) ??
  ((mutexpost_exwt_return_prio_succ (|vl|) ?? mutexpost_exwt_no_return_prio_succ  (|vl|)) ;; 
     isched ;;  END  (Some (Vint32 (Int.repr NO_ERR)))).

Definition mutexpost (vl:vallist):=
  mutexpost_iserr (|vl|) ??
  mutexpost_null (|vl|) ??
  mutexpost_type_err (|vl|) ??
  mutexpost_owner_hold (| vl |) ;; mutexpost_aft_owner  vl.


(* (************************************ q acc  **************************************) *)

Definition MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MSGQ_OVF_ERR := OS_Q_FULL.
Definition MSGQ_NULL_ERR := OS_ERR_PEVENT_NULL.

Definition qacc_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists   v_ret  ,
       vl =  (Vnull :: v_ret :: nil) /\
       opv = Some Vnull/\
       (v_ret = Vnull /\ O_opt = Some O1 \/ 
        v_ret <> Vnull /\ O_opt = None)
  end.

Definition qacc_no_q_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):= 
  match rst with 
  | (opv, O_opt) => 
     (exists qid v_ret, 
       vl= ((Vptr qid) :: v_ret :: nil)/\ 
         ( 
           exists qls,  
             opv =  (Some Vnull)/\ 
              get O1 absecblsid = Some (absecblist qls) /\ 
             (~ exists x y pwl wls,get qls qid = Some (absmsgq x y pwl,wls) )/\ 
              (v_ret = Vnull /\ O_opt = Some O1
              \/ v_ret <>  Vnull /\ O_opt = None)
         ) 
     ) 
  end. 

Definition qacc_no_msg  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):= 
  match rst with
    | (opv, O_opt) =>
     (exists qid v_ret,
       vl= ((Vptr qid):: v_ret :: nil)/\
       ( 
           exists qls, 
             opv =  (Some Vnull)/\
              get O1 absecblsid = Some (absecblist qls) /\
             (exists wls n pwl,get qls qid =Some (absmsgq nil n pwl,wls))/\
              (v_ret = Vnull /\ O_opt = Some O1
              \/ v_ret <>  Vnull /\ O_opt = None)
         )
     )
  end.

Definition qacc_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists qid v_ret,
       vl= ((Vptr qid) :: v_ret :: nil)/\
       (
          exists qls msg mls n pwl wl, 
             opv =  (Some msg)/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq (msg::mls) n pwl,wl)/\
              (v_ret = msg /\ O_opt = Some (set O1 absecblsid (absecblist (set qls qid (absmsgq mls n pwl,wl))))
              \/ v_ret <>  msg /\ O_opt = None)
       )
     )
  end.

Definition qacc_pwl_is_nil  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists qid v_ret,
       vl= ((Vptr qid) :: v_ret :: nil)/\
       (
          exists qls msg mls n pwl wl, 
             opv =  None/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq (msg::mls) n pwl,wl)/\
              (pwl = nil /\ O_opt = Some O1
              \/ pwl <>  nil /\ O_opt = None)
       )
     )
  end.

Definition qacceptnew (vl:vallist):=
  match vl with
    v1 :: vl' =>
      match vl' with
        v2 :: vl'' =>
                qacc_null (|vl|)??
                qacc_no_q_err (|vl|) ??
                qacc_no_msg (|v1 :: v2 :: nil|)??
                (qacc_pwl_is_nil (|vl|) ;; qacc_succ (|vl|))
        | _ => spec_abort
      end 
    | _ => spec_abort
  end.


(* (************************************ q cre  **************************************) *)

Definition Q_SIZE := OS_MAX_Q_SIZE.

Definition qcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists size v' ,
        vl = ((Vint32 size) :: v' :: nil) /\
        opv = Some Vnull /\
        (v'= Vnull /\ O_opt = Some O1 
          \/ v' <> Vnull /\ O_opt = None) 
  end.

Definition qcre_ecb_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists  qls qid t locmp locmp' ptrmp ptrmp',
    exists muxp semp qp,
        vl = nil /\
        opv = None /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls qid = None /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (muxp, semp, qp) /\
        ptrmp' = set ptrmp t (muxp, semp, Vptr qid) /\
        (O_opt = Some (set (set O1 evlocid (evloc locmp')) evptrid (evptr ptrmp'))
         (* \/  O_opt = None  *)
         \/ (exists t', tsk_normal_ev locmp ptrmp t' qid) /\ O_opt = None)
  end. 

Definition qcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' size qid qls t locmp locmp' O',
      vl = ((Vint32 size)  :: v' :: nil) /\
      opv = Some (Vptr qid) /\
      get O1 absecblsid = Some (absecblist qls) /\
      (* Int.ltu (Int.repr Q_SIZE) size=false/\ *)
      get qls qid = None /\
      get O1 evlocid = Some (evloc locmp) /\
      get O1 curtid = Some (oscurt t) /\   
      (*get ptrmp t = Some (muxp, semp, Vptr qid) /\ *)
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
      O' = (set O1 absecblsid (absecblist (set qls qid (absmsgq (nil:list val) size (nil:list tid), (nil:list tid))))) /\
      ((v' = Vptr qid /\ O_opt = Some (set O' evlocid (evloc locmp')))
       \/ (v' <> Vptr qid /\ O_opt = None)) 
  end.

Definition qcre_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists size v' locmp locmp' ptrmp ptrmp' qid t,
      vl = ((Vint32 size)  :: v' :: nil) /\
        opv = (Some Vnull) /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\ 
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\ 
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (Vnull, Vnull, Vptr qid) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        (v'= Vnull /\ O_opt = Some  (set (set O1 evlocid (evloc locmp')) evptrid (evptr ptrmp') )
         \/ v' <> Vnull /\ O_opt = None)
  end.

Definition qcre (vl:vallist):=
  match vl with
    size :: v'  :: nil =>
             qcre_no_free (| size :: v' :: nil |)??
             (qcre_ecb_available (| nil |);; 
              (qcre_err (| size :: v'  :: nil |) ?? qcre_ecb_activate(| size :: v'  ::nil |) ))
  | _ => ABORT 
end.


(* (************************************ q del  **************************************) *)

Definition qdel_null  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
    vl =  (Vnull::nil) /\
    opv =  (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
    O_opt = Some O1
  end.

Definition qdel_no_q_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
    exists qid,
    vl =  ((Vptr qid)::nil) /\  
    (
      exists els,
        get O1 absecblsid = Some (absecblist els) /\
        (~ exists x y wls pwls, get els qid = Some (absmsgq x y pwls,wls)) /\  
        opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
        O_opt = Some O1
    )
  end.

Definition qdel_succ_ex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
    exists qid,
    vl=  ((Vptr qid)::nil) /\
    (
      exists qls qls' x y pwls wls tls tls' tls'',
        exists ptrmp ptrmp' t, 
        opv = None (* (Some (Vint32 (Int.repr NO_ERR))) *) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls qid = Some (absmsgq x y pwls, wls) /\
        (wls <> nil \/ pwls <> nil) /\ 
        join qls' (sig qid (absmsgq x y pwls, wls)) qls /\
        get O1 abstcblsid = Some (abstcblist tls) /\ 
        tls' = set_tls_rdy wls tls /\
        tls'' = set_tls_rdy0 pwls tls' /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get O1 curtid = Some (oscurt t) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        O_opt = Some (set (set (set O1 absecblsid (absecblist qls')) abstcblsid (abstcblist tls'')) evptrid (evptr ptrmp'))
    )
  end.

Definition qdel_succ_nex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
    exists qid,
    vl=  ((Vptr qid)::nil) /\
    (
      exists qls qls' x y pwls wls ptrmp ptrmp' t,
        opv = None (* (Some (Vint32 (Int.repr NO_ERR))) *) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls qid = Some (absmsgq x y nil, nil) /\
        join qls' (sig qid (absmsgq x y pwls, wls)) qls /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get O1 curtid = Some (oscurt t) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\         
        O_opt = Some (set (set O1 absecblsid (absecblist qls')) evptrid (evptr ptrmp'))
    )
  end.  

Definition qdel_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = nil /\
    opv = Some Vnull /\
    O_opt = Some O1
  end.  
  
Definition qdel  (vl: vallist) :=
  match vl with
    v1 :: nil =>
      qdel_null (|vl|) ??
      qdel_no_q_err (|vl|) ??
      (qdel_succ_ex_wait (|vl|);; isched;; qdel_ret (|nil|) ??
        qdel_succ_nex_wait (|vl|);; qdel_ret (|nil|))   
  | _ => ABORT
  end.


(* (************************************ q pend  **************************************) *)

Definition qpend_set_errv
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists errid verr rv errls  , 
       vl = (Vptr errid :: Vint32 verr :: rv :: nil) /\
       get O1 eblsid = Some (eblist errls) /\
       opv = Some rv /\
          ((exists errv,
                get errls errid = Some errv) /\ O_opt = Some (set O1 eblsid (eblist (set errls errid verr)))
                \/ get errls errid = None /\ O_opt = None)
  end.

Definition qpend_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists rv,
        vl = ( rv :: nil) /\
        opv = None /\
        (rv = Vnull /\O_opt =  Some O1 \/
            rv <> Vnull /\ O_opt = None)
  end.

Definition qpend_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists Vnull rv ,
       vl = (Vnull :: rv :: nil) /\
       opv = None /\
       (rv = Vnull /\O_opt =  Some O1 \/
            rv <> Vnull /\ O_opt = None)  
  end.

Definition qpend_no_q_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists qid rv,
         vl= (Vptr qid:: rv ::nil) /\
         exists qls,
                  get O1 absecblsid = Some (absecblist qls) /\
                 (~ exists x y pwls wls,get qls qid = Some (absmsgq x y pwls ,wls) )/\
                 opv = None /\
                 (rv = Vnull /\O_opt =  Some O1 \/
                      rv <> Vnull /\ O_opt = None)        
     )
  end.

Definition qpend_from_idle_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists tls st msg sus t,
      vl = ( nil) /\
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus) /\
       (opv = None /\ O_opt = None)
  end.

Definition qpend_stat_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists tls prio st msg sus t,
      vl = (nil) /\
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio,st,msg,sus) /\ 
           ~ (st = rdy /\ sus = false) /\
       (opv = None /\ O_opt = None)
  end.

Definition qpend_get_no_pwl_succ   (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     ( 
         exists qid rv,
           vl= (Vptr qid :: rv ::nil) /\
           (
             (
(*                exists qls n qls' tcbls tcbls', *)
                  
                 exists t qls tcbls msg ml n wl,
                 exists qls' ,
                  get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\                 
                  get qls qid = Some (absmsgq (msg::ml) n nil ,wl) /\
                  (* get tcbls t = Some (prio,rdy ,m)/\ *)
                  qls'= set qls qid (absmsgq ml n nil,wl)/\
                  (* tcbls' = set tcbls t (prio,rdy ,msg) /\ *) 
                  (*get errls v3 = Some errv /\
                  errls' = set errls v3  ($ OS_NO_ERR) /\ *)
                  opv= None/\
                  (rv = msg /\ O_opt = Some (set O1
                                    absecblsid (absecblist qls'))  
                    \/ rv <> msg /\ O_opt = None)
             )        
           )
     )
  end.

Definition qpend_get_ex_pwl_before_sched   (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     ( 
         exists qid rv, 
           vl= (Vptr qid ::rv ::nil) /\
           (
             (    
                 exists qls tcbls msg  ml n pwl wl prio ,
                 exists qls' tcbls' m t' sus st  ,
                  (* get O1 curtid = Some (oscurt t) /\ *)
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\ 
                  ~ pwl = nil /\               
                  get qls qid = Some (absmsgq (msg::ml) n pwl ,wl) /\
                  (* get tcbls t = Some (prio,rdy ,m)/\ *)
                  qls'= set qls qid (absmsgq (ml++(m::nil)) n (remove_tid t' pwl) ,wl)/\
                  (* tcbls' = set tcbls t (prio,rdy ,msg) /\  *)
                  GetHWait tcbls pwl t' /\
                  get tcbls t' = Some (prio,st,m,sus)/\ 
                  tcbls' = set tcbls t' (prio,rdy,m,sus)/\
                  opv= None/\
                  (rv = msg /\ O_opt = Some (set ( set O1 abstcblsid (abstcblist tcbls'))
                                    absecblsid (absecblist qls'))  
                    \/ rv <> msg /\ O_opt = None)
             )
           )
     )
  end.

Definition qpend_block  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       (
         exists qid v2 m sus,
           vl= (Vptr qid::Vint32 v2 ::nil) /\
           exists tls tls' qls qls' wl p st n t opt_t,
           exists pwl,
               get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq nil n pwl,wl) /\
                 qls'=set qls qid (absmsgq nil n pwl,t::wl)/\
                  get O1 abtcblsid = Some (abstcblist tls) /\ 
                 get tls t = Some (p,st,m,sus) /\
                 ( v2 <> Int.zero /\ opt_t = Some v2 \/ v2 = Int.zero /\ opt_t = None ) /\
                 tls' = set tls t (p,wait (os_stat_q qid) opt_t, m, sus) /\
                 O_opt = Some( set ( set O1 abtcblsid (abstcblist tls') ) 
                                   absecblsid (absecblist qls'))/\
                 opv=  None 
         )
     )
  end.

Definition qpend_to  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid rv,
       vl= (Vptr qid :: rv :: nil) /\
       (
         (
             exists tls piro  t m els els' ml n pwl wl,
              exists sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
              get tls t =Some (piro, wait (os_stat_q qid) (Some Int.zero), m, sus)/\
              m = Vnull /\
              get O1 absecblsid = Some (absecblist els) /\
              get els qid = Some (absmsgq ml n pwl , wl) /\
              In t wl /\
              els' = set els qid (absmsgq ml n pwl, (remove_tid t wl)) /\
            (rv = Vnull /\ O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (piro, rdy, m, false)))) 
                                                        absecblsid (absecblist els'))
               \/ rv <> Vnull /\ O_opt = None)
         )
       )
  end.

Definition qpend_block_get (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid rv,
       vl= (Vptr qid ::rv :: nil) /\
       (
         exists tls p st m sus t  tls',
           get O1 curtid = Some (oscurt t) /\
           get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m,sus)/\
           m<>Vnull /\
           tls' = set tls t (p,rdy,Vnull,false)/\
           (rv = m /\ O_opt = Some ( set O1 abtcblsid (abstcblist tls'))
               \/ rv <> m /\ O_opt = None)
       )
  end.

Definition qpend_set_stat (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid tls prio st msg sus t,
      vl = (Vptr qid :: nil) /\
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio,st,msg,sus) /\ 
           opv = None /\ 
           ( ((st = rdy /\ msg <> Vnull /\ sus = false \/ st = wait (os_stat_q qid) (Some Int.zero) /\ msg = Vnull /\ sus = false)
             /\ O_opt = Some O1) \/ 
             (~(st = rdy /\ msg <> Vnull /\ sus = false \/ st = wait (os_stat_q qid) (Some Int.zero)  /\ msg = Vnull /\ sus = false)
             /\ O_opt = None )    )
  end.

Definition qpendnew (vl:vallist):=
  match vl with
    vp :: vt :: verr :: rv :: nil =>
                (qpend_iserr (| rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_ERR_PEND_ISR) :: rv :: nil|)) ??
                (qpend_null (| vp :: rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_ERR_PEVENT_NULL) :: rv :: nil|)) ??
                (qpend_no_q_err (| vp :: rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_ERR_EVENT_TYPE) :: rv :: nil|)) ??
                qpend_from_idle_err (| nil |) ??
                qpend_stat_err (| nil |) ??
                (qpend_get_no_pwl_succ (| vp :: rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_NO_ERR) :: rv :: nil|)) ??
                (qpend_get_ex_pwl_before_sched (| vp :: rv :: nil |) ;; isched ;;
                        qpend_set_errv (| verr :: Vint32 (Int.repr OS_NO_ERR) :: rv :: nil|)) ??
                (qpend_block (| vp :: vt :: nil |) ;; isched ;; qpend_set_stat (| vp :: nil |) ;;
                     ((qpend_to (| vp :: rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_TIMEOUT) :: rv :: nil|)) ??
                      (qpend_block_get (| vp :: rv :: nil |) ;; qpend_set_errv (| verr :: Vint32 (Int.repr OS_NO_ERR) :: rv :: nil|))  ))
    | _ => spec_abort
  end.


(* (************************************ q post  **************************************) *)

Definition qpost_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists v_msg v_ret,
       vl =  (Vnull :: v_msg :: v_ret :: nil) /\
       opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       (v_ret = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1 \/ 
        v_ret <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None)
  end.

Definition qpost_msg_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid v_ret,
       vl =  ((Vptr qid) :: Vnull :: v_ret :: nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)))/\
       (v_ret = Vint32 (Int.repr OS_ERR_POST_NULL_PTR) /\ O_opt = Some O1 \/
        v_ret <> Vint32 (Int.repr OS_ERR_POST_NULL_PTR) /\ O_opt = None)
  end.

Definition qpost_q_type_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid v_msg v_ret,
       vl =  ( (Vptr qid) :: v_msg :: v_ret :: nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
       exists els ,
              get O1 absecblsid = Some (absecblist els) /\
              (~ exists x y pwl wls,get els qid = Some (absmsgq x y pwl,wls) )/\
       (v_ret = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1 \/ 
        v_ret <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.

Definition qpost_ovf_err(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg v_ret,
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
         (
           exists qls n wl ml pwl,
              opv =  (Some (Vint32 (Int.repr MSGQ_OVF_ERR)))/\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq ml n pwl, wl) /\
                 Z.ge (Z_of_nat (length ml)) (Int.unsigned n)/\ 
            (v_ret = Vint32 (Int.repr MSGQ_OVF_ERR) /\ O_opt = Some O1 \/
             v_ret <> Vint32 (Int.repr MSGQ_OVF_ERR) /\ O_opt = None)
         )
       )
  end.

Definition qpost_nowt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg v_ret,
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
         (
           exists qls n ml pwl,
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq ml n pwl, nil) /\
                 Z.lt (Z_of_nat (length ml)) (Int.unsigned n)/\ 
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ 
                  O_opt = Some ( set O1 absecblsid (absecblist (set qls qid (absmsgq (ml++(msg::nil)) n pwl,nil)))) \/
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition qpost_exwt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg v_ret,
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
         (
           exists qls vl wl qls' t' tls tls' m,  
           exists p st n pwl sus,
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 abstcblsid = Some (abstcblist tls) /\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq vl n pwl,wl) /\
                 ~ wl =nil /\
                 GetHWait tls wl t'/\
                 get tls t' = Some (p,st,m,sus)/\
                 tls'=set tls t' (p,rdy,msg,sus)/\
                 qls' = set qls qid (absmsgq nil n pwl,(remove_tid t' wl) )/\
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\
                   O_opt =Some ( set ( set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist qls') ) \/
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition qpost_exwt_abt(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg v_ret,
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
           exists  qls vl n pwl wl ,  

               get O1 absecblsid = Some (absecblist qls) /\
               get qls qid = Some (absmsgq vl n pwl,wl) /\
               ~ wl =nil /\
               opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = None
       )
  end.

Definition qpost (vl:vallist):=
  match vl with
    v1 :: vl' =>
      match vl' with
        v2 :: vl'' =>
          match vl'' with
            v3 :: nil =>
                qpost_null (|vl|)??
                qpost_msg_null (|vl|) ??
                (* qpost_q_not_in_dom_abt (|v1 :: v2 :: nil|)?? *)
                qpost_q_type_err (|vl|) ??
                qpost_ovf_err (|vl|) ?? 
                qpost_nowt_succ  (|vl|) ??
                ( (qpost_exwt_succ (|vl|) ?? qpost_exwt_abt(|vl|)) ;; 
                  isched ;; 
                  END (Some (Vint32 (Int.repr OS_NO_ERR))) )
             | _ => spec_abort
           end 
        | _ => spec_abort
      end 
    | _ => spec_abort
  end.

(* (************************************ IPCQPost  **************************************) *)

Definition ipcqpost (vl:vallist):=
  match vl with
    v1 :: vl' =>
      match vl' with
        v2 :: vl'' =>
          match vl'' with
            v3 :: nil =>
                qpost_null (|vl|)??
                qpost_msg_null (|vl|) ??
                qpost_q_type_err (|vl|) ??
                qpost_ovf_err (|vl|) ?? 
                qpost_nowt_succ  (|vl|) ??
                ( (qpost_exwt_succ (|vl|) ?? qpost_exwt_abt(|vl|)) ;; 
                  (* isched ;;  *)
                  END (Some (Vint32 (Int.repr OS_NO_ERR))) )
             | _ => spec_abort
           end 
        | _ => spec_abort
      end 
    | _ => spec_abort
  end.


(* (************************************ q timedpost  **************************************) *)

Definition qtimedpost_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists  time msg v_ret,
       vl =  (Vnull :: time :: msg :: v_ret :: nil) /\
       opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))/\
       (v_ret = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1 \/ 
        v_ret <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None)
  end.

Definition qtimedpost_msg_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time v_ret,
       vl =  ((Vptr qid) :: time :: Vnull :: v_ret :: nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_POST_NULL_PTR)))/\
       (v_ret = Vint32 (Int.repr OS_ERR_POST_NULL_PTR) /\ O_opt = Some O1 \/
        v_ret <> Vint32 (Int.repr OS_ERR_POST_NULL_PTR) /\ O_opt = None)
  end.

Definition qtimedpost_q_type_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret,
       vl =  ( (Vptr qid) :: time :: msg :: v_ret :: nil) /\
       opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\
       exists els ,
              get O1 absecblsid = Some (absecblist els) /\
              (~ exists x y pwl wls,get els qid = Some (absmsgq x y pwl,wls) )/\
       (v_ret = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1 \/ 
        v_ret <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.

Definition  qtimedpost_prio_idle_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg sus v_ret,
       vl =  ( (Vptr qid) :: time :: msg :: v_ret :: nil) /\
         exists tls st msg t,
           get O1 curtid = Some (oscurt t) /\
           get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus) /\
       opv = None/\
       O_opt = None 
  end.

Definition qtimedpost_stat_not_rdy (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg sus v_ret,
       vl =  ( (Vptr qid) :: time :: msg :: v_ret :: nil) /\
         exists tls st msg prio t,
           get O1 curtid = Some (oscurt t) /\
           get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg,sus) /\
           ~(st = rdy /\ sus = false) /\
       opv = None/\
       O_opt = None 
  end.

Definition qtimedpost_ovf_block(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg sus p st m time v_ret, 
       vl= (Vptr qid :: Vint32 time :: msg :: v_ret :: nil) /\
       (
           exists t qls qls' tls tls' ml n pwl wl ,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get qls qid = Some (absmsgq ml n pwl, wl) /\
              Z.ge (Z_of_nat (length ml)) (Int.unsigned n) /\
              qls' = set qls qid (absmsgq ml n (t :: pwl), wl) /\
              get tls t = Some (p,st,m,sus) /\
              tls' = set tls t (p,wait (os_stat_postq qid) None,msg,sus)/\
              opv = None /\
              O_opt =Some ( set ( set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist qls') ) 
       )
  end.

Definition qtimedpost_after_sched (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists qid time msg v_ret ,
       vl= (Vptr qid :: time :: msg :: v_ret ::nil) /\
       (
         (
           exists tls p st t m sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, st, m, sus)/\
              opv = None /\
              (( ((st = rdy /\ sus = false)  \/ ( st = wait (os_stat_postq qid) None /\ sus = false))  /\ O_opt = Some O1)
              \/ 
              ( ~((st = rdy /\ sus = false) \/ ( st = wait (os_stat_postq qid) None /\ sus = false) ) /\ O_opt = None))
         )
       )
  end.

Definition qtimedpost_timeout_err(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret  , 
       vl= (Vptr qid :: time :: msg :: v_ret ::nil) /\
       (
           exists t tls p m sus qls qls' ,
           exists pwl n ml wl,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t = Some (p, wait (os_stat_postq qid) None,m,sus) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get qls qid = Some (absmsgq ml n pwl, wl) /\
              In t pwl /\
              qls' = set qls qid (absmsgq ml n (remove_tid t pwl), wl)/\
               (* m = Vnull /\  *)
              opv =  (Some (Vint32 (Int.repr OS_TIMEOUT)))/\
              ( v_ret = Vint32 (Int.repr OS_TIMEOUT) /\ 
                  O_opt = Some ( set (set O1 abstcblsid( abstcblist (set tls t (p, rdy,Vnull, false))) ) 
                  absecblsid (absecblist qls')) 
              \/ v_ret <> Vint32 (Int.repr OS_TIMEOUT) /\ O_opt = None) 
       )
  end.

Definition qtimedpost_block_post_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret , 
       vl= (Vptr qid :: time :: msg :: v_ret ::nil) /\
       (
           exists t   tls  p st m sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t = Some (p,st,m,sus) /\
               st = rdy /\ sus = false /\
               opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
               (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ O_opt = Some O1 \/
                v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
        )
  end. 

Definition qtimedpost_nowt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret,
       vl= (Vptr qid :: time :: msg ::v_ret :: nil) /\
       (
         (
           exists qls n ml pwl,
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq ml n pwl, nil) /\
                 Z.lt (Z_of_nat (length ml)) (Int.unsigned n)/\ 
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ 
                  O_opt = Some ( set O1 absecblsid (absecblist (set qls qid (absmsgq (ml++(msg::nil)) n pwl,nil)))) \/
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition qtimedpost_exwt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret,
       vl= (Vptr qid :: time :: msg ::v_ret :: nil) /\
       (
         (
           exists qls vl wl qls' t' tls tls' m sus,  
           exists p st n pwl,
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 abstcblsid = Some (abstcblist tls) /\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq vl n pwl,wl) /\
                 ~ wl =nil /\
                 GetHWait tls wl t'/\
                 get tls t' = Some (p,st,m,sus)/\
                 tls'=set tls t' (p,rdy,msg,sus)/\
                 qls' = set qls qid (absmsgq nil n pwl,(remove_tid t' wl) )/\
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\
                   O_opt =Some ( set ( set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist qls') ) \/
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition qtimedpost_exwt_abt(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret,
       vl= (Vptr qid :: time :: msg ::v_ret :: nil) /\
       (
           exists  qls vl n pwl wl ,
               get O1 absecblsid = Some (absecblist qls) /\
               get qls qid = Some (absmsgq vl n pwl,wl) /\
               ~ wl =nil /\
               opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = None
       )
  end.

Definition qtimedpost (vl:vallist):=
  match vl with
    pevent :: timeout :: msg :: rv =>
                      qtimedpost_null (|vl|)??
                      qtimedpost_msg_null (|vl|) ??
                      (* qtimedpost_q_not_in_dom_abt (|pevent :: nil|)?? *)
                      qtimedpost_q_type_err (|vl|) ??
                      ( (qtimedpost_exwt_succ (|vl|) ?? qtimedpost_exwt_abt(|vl|) ) ;; 
                          isched ;; 
                          END (Some (Vint32 (Int.repr OS_NO_ERR))) )??
                      qtimedpost_stat_not_rdy (|vl|) ??
                      qtimedpost_prio_idle_err (|vl|) ??
                      (qtimedpost_ovf_block (|vl|) ;; isched ;; 
                           qtimedpost_after_sched (|vl|) ;;
                          (qtimedpost_timeout_err (|vl|) ??  qtimedpost_block_post_succ (|vl|)) )??
                      qtimedpost_nowt_succ  (|vl|) 
  | _ => spec_abort
end.


(* (************************************ q query  **************************************) *)

(* from os_inv.v *)
Definition id_addrval' (v : val) (id :var) (t : type):=
     match v with
     | Vptr av => id_addrval av id t
     | _ => None
    end.

Definition qquery_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists   v_ret pdata ,
       vl =  (Vnull :: pdata ::v_ret :: nil) /\
       opv = Some (V$ OS_ERR_PEVENT_NULL)/\
       (v_ret = (V$ OS_ERR_PEVENT_NULL) /\ O_opt = Some O1 \/ 
        v_ret <> (V$ OS_ERR_PEVENT_NULL) /\ O_opt = None)
  end.

Definition qquery_null_not_legal_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid v_ret pdata els,
      vl = (Vptr qid :: pdata :: v_ret:: nil) /\
      get O1 absecblsid = Some (absecblist els) /\
      get els qid = None /\
       (opv = None /\ O_opt = None)
  end.

Definition qquery_no_q_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):= 
  match rst with 
  | (opv, O_opt) => 
     (exists qid v_ret pdata, 
       vl= ((Vptr qid) :: pdata :: v_ret :: nil)/\ 
         ( 
           exists qls,  
             opv =  (Some (V$ OS_ERR_EVENT_TYPE))/\ 
              get O1 absecblsid = Some (absecblist qls) /\ 
             (~ exists x y pwl wls,get qls qid = Some (absmsgq x y pwl,wls) )/\ 
              (v_ret = (V$ OS_ERR_EVENT_TYPE) /\ O_opt = Some O1
              \/ v_ret <>  (V$ OS_ERR_EVENT_TYPE) /\ O_opt = None)
         ) 
     ) 
  end. 

Definition qquery_pdata_validptr_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pdata evheap t vl l,
   vl = ((Vptr pdata) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap pdata = None \/
        (Get_struct evheap pdata = Some (pdata, t, l) /\ t <> OS_Q_DATA) ) /\
   opv = None /\
   O_opt = None
end.

Definition qquery_succ_if  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists qid pdata v_ret,
       vl= ((Vptr qid) :: Vptr pdata :: v_ret :: nil)/\ 
       (
          exists qls msg mls n pwl wl l  arrayheap l2 , 
          exists evheap evheap' evheap'' evheap''' evheap'''' ,
          exists  (qletbl : addrval) arrayheap' ,
             opv =  (Some (V$ OS_NO_ERR))/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq (msg::mls) n pwl,wl)/\
             get O1 evstructheapid = Some (evstructheap evheap) /\
             Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) /\
             (exists i0,evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) /\ 
             (evheap'' = Set_struct' evheap' pdata OSMsg  (msg))  /\
             (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(msg::mls)))) ) /\
             (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  /\
             
             get O1 evarrayheapid = Some (evarrayheap arrayheap) /\
             id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl /\
             Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) /\ 
             (exists l2', arrayheap' = Set_array' arrayheap qletbl l2') /\ 
              (v_ret = V$ OS_NO_ERR /\ O_opt = Some (set ( set O1 evarrayheapid (evarrayheap arrayheap')) evstructheapid (evstructheap evheap''''))
              \/ v_ret <>  V$  OS_NO_ERR /\ O_opt = None)
       )
     )
  end.
  
Definition qquery_succ_else  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists qid pdata v_ret,
       vl= ((Vptr qid) :: Vptr pdata :: v_ret :: nil)/\ 
       (
          exists qls mls n pwl wl l  arrayheap l2 , 
          exists evheap evheap' evheap'' evheap''' evheap'''' ,
          exists  (qletbl : addrval) arrayheap' ,
             opv =  (Some (V$ OS_NO_ERR))/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq mls n pwl,wl)/\
             get O1 evstructheapid = Some (evstructheap evheap) /\
             Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) /\
             (exists i0,evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) /\ 
             (evheap'' = Set_struct' evheap' pdata OSMsg  (Vnull))  /\
             (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (V$ (Z.of_nat(length(mls)))) ) /\
             (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  /\
             
             get O1 evarrayheapid = Some (evarrayheap arrayheap) /\
             id_addrval' (Vptr pdata) code.os_code_defs.OSEventTbl OS_Q_DATA = Some qletbl /\
             Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) /\ 
             (exists l2', arrayheap' = Set_array' arrayheap qletbl l2') /\ 
              (v_ret = V$ OS_NO_ERR /\ O_opt = Some (set ( set O1 evarrayheapid (evarrayheap arrayheap')) evstructheapid (evstructheap evheap''''))
              \/ v_ret <>  V$  OS_NO_ERR /\ O_opt = None)
       )
     )
  end.

Definition qquerynew (vl:vallist) :=
  match vl with
      rv_ptr :: pdata :: rv_post :: nil =>
          qquery_null(|rv_ptr :: pdata :: rv_post::nil |)??
          qquery_null_not_legal_err(|rv_ptr :: pdata :: rv_post::nil |)??
          qquery_no_q_err (|rv_ptr :: pdata :: rv_post::nil |)??
          qquery_pdata_validptr_err(|pdata :: nil |)??
          qquery_succ_if(|rv_ptr:: pdata ::rv_post::nil|)??
          qquery_succ_else(|rv_ptr:: pdata ::rv_post::nil|)
      | _ => spec_abort
  end.

(* end abs ops for internal functions for events *)


(* abs ops for GJB functions for events *) 

(* (****************************** sem_trywait ************************************) *)
Definition semtrywait_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = v :: v' :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition semtrywait_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition semtrywait_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv, 
      vl = ((Vint32 posv) :: rv :: nil) /\ 
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semtrywait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo e tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/
            e = infonull /\ v' = Vnull) 
           /\ O_opt = Some O1 
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
  end.

Definition semtrywait_get_ecb_ptr1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo e tp sc ptrmp ptrmp' t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          ((e = infonull /\ v' = Vnull /\ ptrmp' = ptrmp) 
           /\ O_opt = Some O1)
           \/ (v' <> Vnull /\ O_opt = None) 
  end.

Definition semtrywait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc ptrmp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull))))
           \/ (v' <> Vptr eid /\ O_opt = None))
  end.

Definition semtrywait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp, sc) /\
          O_opt = None 
  end.

Definition semtrywait_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.mone) /\ O_opt = None))
  end. 

Definition semtrywait_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition semtrywait_after_acc_1
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v t ptrmp ptrmp' v',
    vl = (Vint32 v) :: v' :: nil /\
    Int.ltu Int.zero v = true /\
    get O1 curtid = Some (oscurt t) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
    (v' = Vint32 (Int.zero) /\ opv = Some v' /\ O_opt = Some (set O1 evptrid (evptr ptrmp')) 
     \/ v' <> Vint32 (Int.zero) /\ O_opt = None)
  end.

Definition semtrywait_after_acc_2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v t ptrmp ptrmp' v',
    vl = (Vint32 v) :: v' :: nil /\
    Int.ltu Int.zero v = false /\
    get O1 curtid = Some (oscurt t) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
    (v' = Vint32 (Int.mone) /\ opv = Some v' /\ O_opt = Some (set O1 evptrid (evptr ptrmp'))
     \/ v' <> Vint32 (Int.mone) /\ O_opt = None)
  end.

(* H: EX vl', semtrywait ((rev vl) ++ vl') *)
(* vl = v1 :: v2 :: v3 :: v4 :: nil *)
Definition semtrywait (vl: vallist) :=
  match vl with
    vsm :: v1 :: v20 :: v2 :: v3 :: v4 ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semtrywait_semerr (| vsm::v1::nil |) ?? semtrywait_sem_pos (| vsm::v1::nil |));; 
      (semtrywait_poserr (| v1::v4::nil |) ??  
         (semtrywait_get_ecb_ptr (| v1::v20::nil |);; 
          (semtrywait_if_null_yes (| v20::v4::nil |) ?? 
             (semtrywait_if_null_no (| v20::nil |);;
               partition_pos_rgn (v1 :: vr_temp_dom :: vr_temp_num ::
                                                    vr_temp_dom' :: vr_temp_num' :: (* v4 :: *) nil)
              ((semtrywait_get_ecb_ptr1 (| v1::v2::nil |) ?? semtrywait_get_ecb_ptr2 (| v1::v2::nil |) ??
               semtrywait_ecb_ptr_holder_abt (| v1::v2::nil |));;
              semacc (v2::v3::nil);;
              (semtrywait_after_acc_1 (| v3::v4::nil |) ??
                 semtrywait_after_acc_2 (| v3::v4::nil |)) ) ))))
  | _ => spec_abort
  end.

Definition semtrywaitapi :=(semtrywait, (Tint32, Tptr sem_t::nil)).


(* (****************************** sem_init ************************************) *) 

Definition seminit_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
        vl = ( nil) /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition seminit_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vsem,
      vl = vsem :: nil /\
        (vsem = Vnull \/
           exists a,
             vsem = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition seminit_valerr
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists val,
    vl = Vint32 val :: nil /\
    Int.ltu (Int.repr SEM_VALUE_MAX) val = true /\
    opv = Some (Vint32 (Int.mone)) /\
    O_opt = Some O1
  end.

Definition seminit_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo cpn idx left right, 
      vl = (posv :: Vint32 idx :: Vint32 cpn :: nil) /\
       get O1 seminfoid = Some (seminfo semifo) /\
       left = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx)%Z /\
       right = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1))%Z /\
      (
      ((~(exists pos tp sc, get semifo pos = Some (infonull, tp, sc) /\ 
                         (left <= (Int.unsigned pos) < right)%Z) /\
          posv = Vint32 (Int.repr 255)) \/
       (exists pos tp sc, get semifo pos = Some (infonull, tp, sc) /\
         posv = Vint32 pos )) /\ O_opt = Some O1
      ) \/
      (
      ((~(exists pos tp sc, get semifo pos = Some (infonull, tp, sc) /\ 
                         (left <= (Int.unsigned pos)  < right)%Z) /\
      posv <> Vint32 (Int.repr 255)) \/
     (exists pos tp sc, get semifo pos = Some (infonull, tp, sc) /\
      posv <> Vint32 pos )) /\ O_opt = None
      )
end.

Definition seminit_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos, 
      vl = ((Vint32 pos) :: nil) /\ 
      Int.eq pos (Int.repr 255) = true /\
      opv = Some (Vint32 (Int.mone)) /\
      O_opt = Some O1
  end.

(* set ECB pointer in EIB to the placeholder *)
(* update the ghost location and index to reflect the status of creating a sem. *) 
Definition seminit_set_placeholder
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos semifo e tp sc,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp, sc) /\
      opv = None /\
      O_opt = Some (set O1 seminfoid (seminfo (set semifo pos (infohold, tp, sc))))
  end.

Definition seminit_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t semifo e tp sc semifo',
    exists locmp locmp' ptrmp ptrmp' muxp semp qp,
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp, sc) /\
      get O1 curtid = Some (oscurt t) /\
      get O1 evlocid = Some (evloc locmp) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\
      get O1 evptrid = Some (evptr ptrmp) /\
      get ptrmp t = Some (muxp, semp, qp) /\
      ptrmp' = set ptrmp t (muxp, Vnull, qp) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr /\ semifo' = set semifo pos (infotid eid, tp, sc))) 
        \/ eptr = Vnull /\ semifo' = set semifo pos (infonull, tp, sc)) /\  
       O_opt = Some (set (set (set O1 seminfoid (seminfo semifo')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
  end.

Definition seminit_holder_abt
           (vl: vallist) (O: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = Vptr vhold_addr :: nil /\ O_opt = None
  end.

Definition seminit_create_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos, 
    vl = (Vint32 pos :: Vnull :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    opv = Some (Vint32 (Int.mone)) /\
    O_opt = Some O1 
  end.

Definition seminit_set_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos e semifo tp sc semifo', 
      vl = (Vint32 pos) :: nil /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp, sc) /\ 
      opv = None /\
      semifo' = set semifo pos (e, Int.repr SEM_COUNTING, sc) /\
      O_opt = Some (set O1 seminfoid (seminfo semifo')) 
  end.

Definition seminit_set_sem
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a pos pbls,
      vl = (Vptr a) :: (Vint32 pos) :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = Some (Vint32 (Int.zero)) /\
        (((exists posv, get pbls a = Some posv) /\ O_opt = Some (set O1 pblsid (pblist (set pbls a pos))))
          \/ ~(exists posv, get pbls a = Some posv) /\ O_opt = None)
  end.

(* H: EX vl', seminit ((rev vl) ++ vl') *)
(* vl = vsm :: value :: posv :: vr_cre :: nil *)
Definition seminit (vl: vallist) :=
  match vl with
    vsm :: value :: posv :: vr_cre :: vr_temp_dom :: vr_temp_num :: nil => 
      seminit_iserr (| nil |) ??
      seminit_semerr (| vsm :: nil |) ??
        seminit_valerr (| value :: nil |) ??
        (kscurdom_ext (| nil |) ;; 
         get_temp_dom (| vr_temp_dom :: nil |) ;;
         get_temp_num (| vr_temp_num :: nil |) ;;
         seminit_pos (| posv :: vr_temp_dom :: vr_temp_num :: nil |);;
         (seminit_poserr (|posv :: nil|) ??
            (seminit_set_placeholder (|posv :: nil|) ;; 
             semcre (value :: vr_cre :: nil) ;;
             (seminit_set_ecb_ptr (| posv :: vr_cre :: nil |) ?? seminit_holder_abt (| vr_cre :: nil|));;  
             (seminit_create_err (| posv :: vr_cre :: nil |) ?? 
              (* seminit_emb_hold_after_ecb (| posv :: vr_cre :: nil |) ;; *)
              seminit_set_type (| posv :: nil |) ;;
              seminit_set_sem (| vsm :: posv :: nil |) ) ))) 
  | _ => spec_abort
  end.

Definition seminitapi := (seminit, (Tint32, Tptr sem_t :: unsigned_int :: nil)). 


(* (****************************** sem_init_bin ************************************) *) 

Definition seminit_set_type_bin
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos e semifo tp sc semifo', 
      vl = (Vint32 pos) :: nil /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp, sc) /\ 
      opv = None /\
      semifo' = set semifo pos (e, Int.repr SEM_BINARY, sc) /\
      O_opt = Some (set O1 seminfoid (seminfo semifo')) 
  end.

(* H: EX vl', seminit ((rev vl) ++ vl') *)
(* vl = vsm :: value :: posv :: vr_cre :: nil *)
Definition seminitbin (vl: vallist) :=
  match vl with
    vsm :: value :: posv :: vr_cre :: vr_temp_dom :: vr_temp_num :: nil => 
      seminit_iserr (| nil |) ??
      seminit_semerr (| vsm :: nil |) ??
        seminit_valerr (| value :: nil |) ??
        (kscurdom_ext (| nil |) ;;
         get_temp_dom (| vr_temp_dom :: nil |) ;;
         get_temp_num (| vr_temp_num :: nil |) ;;
         seminit_pos (| posv :: vr_temp_dom :: vr_temp_num :: nil |);;
         (seminit_poserr (|posv :: nil|) ??
            (seminit_set_placeholder (|posv :: nil|) ;; 
             semcre (value :: vr_cre :: nil) ;;
             (seminit_set_ecb_ptr (| posv :: vr_cre :: nil |) ?? seminit_holder_abt (| vr_cre :: nil|));;  
             (seminit_create_err (| posv :: vr_cre :: nil |) ?? 
              (* seminit_emb_hold_after_ecb (| posv :: vr_cre :: nil |) ;; *)
              seminit_set_type_bin (| posv :: nil |) ;;
              seminit_set_sem (| vsm :: posv :: nil |) ) ))) 
  | _ => spec_abort
  end.

Definition seminitbinapi := (seminitbin, (Tint32, Tptr sem_t :: unsigned_int :: nil)). 


(* (****************************** sem_destroy ************************************) *)

Definition semdestroy_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
      vl = v :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semdestroy_sem_nopblk_abt
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a',
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = None /\ 
      O_opt = None
  end.

Definition semdestroy_pos_err 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\
      (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ 
       Int.eq posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\  
      opv = Some (Vint32 (Int.mone)) /\ 
       O_opt = Some O1
  end.

Definition semdestroy_pevent_null_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.mone)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr  (OS_USER_MAX_EVENTS / 3)) = true) /\    
      exists semeibs tp sc,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infonull, tp, sc) /\ 
        O_opt = Some O1 
  end.

Definition semdestroy_not_placeholder_assm
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr  (OS_USER_MAX_EVENTS / 3)) = true) /\
      exists semeibs tp sc,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infohold, tp, sc) /\
        O_opt = None
  end.

Definition semdestroy_waiting_tasks_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.mone)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\ 
      exists semeibs tp sc els n wls eid,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infotid eid, tp, sc) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (abssem n, wls) /\
        wls <> nil /\
        O_opt = Some O1
  end.

Definition semdestroy_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
       exists v,
        vl = (v :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
         O_opt = Some O1
  end.

Definition semdestroy_succ (vl: vallist) (O1: osabst) (rst: option val *option osabst) := 
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.zero)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\    
      exists semeibs semeibs' tp sc els n eid els',
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infotid eid, tp, sc) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (abssem n, nil) /\
        join els' (sig eid (abssem n, nil)) els /\
        semeibs' = set semeibs posv (infonull, tp, sc) /\ 
        O_opt = Some (set (set O1 absecblsid (absecblist els')) seminfoid (seminfo semeibs'))
  end.

Definition semdestroy (vl: vallist) :=
  match vl with
    v1 :: nil => 
      semdestroy_semerr (| vl |) ??
      semdestroy_sem_nopblk_abt (| vl |) ?? 
      semdestroy_pos_err (| vl |) ??
      semdestroy_not_placeholder_assm (| vl |) ??
      semdestroy_pevent_null_err (| vl |) ??
      (kscurdom_ext (| nil |) ;; partition_pos_out_of_rgn_err (| vl |)) ??
      semdestroy_waiting_tasks_err (| vl |) ??
      semdestroy_iserr (| vl |) ??
      semdestroy_succ (| vl |) 
  | _ => ABORT
  end.

Definition semdestroyapi := (semdestroy, (Tint32, Tptr sem_t :: nil)).


(* (****************************** sem_wait ************************************) *)  

Definition semwait_iserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = nil /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semwait_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = v :: v' :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition semwait_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition semwait_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv, 
      vl = ((Vint32 posv) :: rv :: nil) /\ 
      (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semwait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp sc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
  end.

Definition semwait_get_ecb_ptr1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc ptrmp ptrmp' t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infonull, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          ((v' = Vnull /\ ptrmp' = ptrmp) /\ O_opt = Some O1) 
           \/ (v' <> Vnull /\ O_opt = None) 
  end.

Definition semwait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc ptrmp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull))))
           \/ (v' <> Vptr eid /\ O_opt = None))
  end.

Definition semwait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp, sc) /\
          O_opt = None 
  end.

Definition semwait_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.mone) /\ O_opt = None))
  end. 

Definition semwait_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition semwait_after_pend_1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp' v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.ltu Int.zero v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        (v' = Vint32 (Int.mone) /\ opv = Some v' /\ O_opt = Some (set O1 evptrid (evptr ptrmp')) 
         \/ v' <> Vint32 (Int.mone) /\ O_opt = None) 
  end.

Definition semwait_after_pend_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp' v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.ltu Int.zero v = false /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        opv = Some (Vint32 (Int.zero)) /\
        (v' = Vint32 (Int.zero) /\ opv = Some v' /\ O_opt = Some (set O1 evptrid (evptr ptrmp'))
         \/ v' <> Vint32 (Int.zero) /\ O_opt = None) 
  end.

Definition semwait_afteraddcheck (vl: vallist) :=
  match vl with
    v1 :: v20 :: v2 :: v3 :: v4 :: 
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semwait_poserr (|v1::v4::nil|) ??  
         (semwait_get_ecb_ptr (|v1::v20::nil|);; 
          (semwait_if_null_yes (| v20::v4::nil |) ?? 
             (semwait_if_null_no (| v20::nil |);;
              partition_pos_rgn (v1 :: vr_temp_dom :: vr_temp_num ::
                                                  vr_temp_dom' :: vr_temp_num' :: (* v4 :: *) nil)
              ((semwait_get_ecb_ptr1 (|v1::v2::nil|) ?? semwait_get_ecb_ptr2 (|v1::v2::nil|) ?? 
               semwait_ecb_ptr_holder_abt (|v1::v2::nil|));;  
              (spec_code_cons 
                 (sem_pend (v2:: (Vint32 Int.zero) :: v3 :: nil))
                 (semwait_after_pend_1 (|v3::v4::nil|) ??
                    semwait_after_pend_2 (|v3::v4::nil|))))  )))) 
  | _ => spec_abort
  end.

(* H: EX vl', semwait ((rev vl) ++ vl') *)
(* vl = vsm :: v1 :: v20 :: v2 :: v3 :: v4 :: nil *) 
Definition semwait (vl: vallist) :=
  match vl with
    vsm :: v1 :: v20 :: v2 :: v3 :: v4 ::
     vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semwait_iserr (| nil |) ??
         ((semwait_semerr (|vsm::v1::nil|) ?? semwait_sem_pos (|vsm::v1::nil|));; 
          semwait_afteraddcheck (v1 :: v20 :: v2 :: v3 :: v4 :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil)))
  | _ => spec_abort
  end.

Definition semwaitapi := (semwait, (Tint32, Tptr sem_t :: nil)). 


(* (****************************** sem_timedwait ************************************) *)

Definition semtimedwait_iserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = nil /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semtimedwait_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = v :: v' :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition semtimedwait_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition semtimedwait_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv,
      vl = ((Vint32 posv) :: nil) /\ 
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
       O_opt = Some O1 /\ opv = Some (Vint32 (Int.mone)) 
  end.

Definition semtimedwait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
  end.

Definition semtimedwait_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
(*       exists, *)
      (vl = Vnull :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
       O_opt = Some O1
  end. 

Definition semtimedwait_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition semtimedwait_get_ecb_ptr1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc ptrmp ptrmp' t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infonull, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          ((v' = Vnull /\ ptrmp' = ptrmp) /\ O_opt = Some O1) 
           \/ (v' <> Vnull /\ O_opt = None) 
  end.

Definition semtimedwait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc ptrmp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp, sc) /\
          get O1 evptrid = Some (evptr ptrmp) /\
          get O1 curtid = Some (oscurt t) /\
          get ptrmp t = Some (Vnull, Vnull, Vnull) /\
          (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull))))
           \/ (v' <> Vptr eid /\ O_opt = None))
  end.

Definition semtimedwait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp, sc) /\
          O_opt = None 
  end.

Definition semtimedwait_timeout_err 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists timeout, 
      vl = ((Vint32 timeout) :: nil) /\ 
       ( Int.ltu (Int.repr 65535) timeout = true \/ timeout =(Int.repr 0)) /\
       opv = Some (Vint32 (Int.mone))/\ 
       O_opt = Some O1
  end.

Definition semtimedwait_after_pend_timeout
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp' ,
      vl = (Vint32 v)  :: nil /\
        Int.eq (Int.repr OS_TIMEOUT) v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        opv = Some (Vint32 (Int.mone)) /\
         O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end.

Definition semtimedwait_after_pend_1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp' ,
      vl = (Vint32 v)  :: nil /\
        Int.ltu Int.zero v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end.

Definition semtimedwait_after_pend_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp' ,
      vl = (Vint32 v)  :: nil /\
        Int.ltu Int.zero v = false /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
       opv = Some (Vint32 (Int.zero)) /\
        O_opt = Some (set O1 evptrid (evptr ptrmp'))  
  end.

Definition semtimedwait_afteraddcheck (vl: vallist) :=
  match vl with
    vtime :: v1 :: v20 :: v2 :: v3 :: 
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semtimedwait_poserr (|v1::nil|) ?? 
         (semtimedwait_get_ecb_ptr (|v1::v20::nil|);; 
          (semtimedwait_if_null_yes (| v20::nil |) ?? 
             (semtimedwait_if_null_no (| v20::nil |);;
              partition_pos_rgn (v1 :: vr_temp_dom :: vr_temp_num ::
                                                                vr_temp_dom' :: vr_temp_num' :: nil)
              ((semtimedwait_timeout_err (|vtime::nil|) ?? 
              (semtimedwait_get_ecb_ptr1 (|v1::v2::nil|) ?? semtimedwait_get_ecb_ptr2 (|v1::v2::nil|) ?? 
               semtimedwait_ecb_ptr_holder_abt (|v1::v2::nil|));; 
              (spec_code_cons 
                 (sem_pend (v2:: vtime :: v3 :: nil))
                 (semtimedwait_after_pend_timeout (|v3::nil|) ??
                            semtimedwait_after_pend_1 (|v3::nil|) ??
                            semtimedwait_after_pend_2 (|v3::nil|) ))) ) )))) 
  | _ => spec_abort
  end.

Definition semtimedwait (vl: vallist) :=
  match vl with
    vsm :: vtime :: v1 :: v20 :: v2 :: v3 :: 
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semtimedwait_iserr (| nil |) ??
         ((semtimedwait_semerr (|vsm::v1::nil|) ?? semtimedwait_sem_pos (|vsm::v1::nil|));; 
          semtimedwait_afteraddcheck (vtime :: v1 :: v20 :: v2 :: v3 :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' ::  nil)))
  | _ => spec_abort
  end.

Definition semtimedwaitapi := (semtimedwait, (Tint32, Tptr sem_t :: Tint16 ::nil)).


(* (****************************** sem_post ************************************) *)

Definition semsignal_semerr
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v v',
    vl = v :: v' :: nil /\
    (v = Vnull \/
     exists a,
       v = Vptr a /\ 
       (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
    ) /\ 
    opv = None /\
    (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
     v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition semsignal_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.


Definition semsignal_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv  rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semsignal_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp sc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
end.

Definition semsignal_get_ecb_ptr1 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo ptrmp t tp sc,
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infonull, tp, sc) /\
    get O1 evptrid = Some (evptr ptrmp) /\ 
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition semsignal_get_ecb_ptr2 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo eid ptrmp t tp sc,  
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infotid eid, tp, sc) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull)))) \/ 
     v' <> Vptr eid /\ O_opt = None) 
  end.

Definition semsignal_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp sc, 
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infohold, tp, sc) /\
    O_opt = None 
  end.

Definition semsigna_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition semsigna_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition semsignal_eid_not_hold 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e tp sc, 
        vl = ((Vint32 posv) :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\ 
          ((exists eid, e = infotid eid  \/ e = infonull )
           /\ O_opt = Some O1
            \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) 
             /\ O_opt = None) )
end.

Definition semsignal_binary_ovf
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      exists rv posv semifo eid tp sc,
      exists els n wl,
        vl = ((Vint32 posv) :: rv :: nil) /\
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          EmbMod.get semifo posv = Some (infotid eid, tp, sc) /\
          tp = (Int.repr 1)/\
          get O1 absecblsid = Some (absecblist els) /\
          get els eid = Some (abssem n, wl) /\
(*           (n = Int.one \/ Int.lt Int.one n = true)/\ *)
          (Int.eq n Int.one = true\/ Int.ltu Int.one n = true) /\
        (rv = (Vint32 Int.zero) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 Int.zero /\ O_opt = None)
  end.

Definition semsignal_after_post_1
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v t ptrmp ptrmp' v', 
    vl = (Vint32 v) :: v' :: nil /\
    v = Int.zero /\
    get O1 curtid = Some (oscurt t) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
    opv = Some (Vint32 Int.zero) /\  
    (v' = Vint32 (Int.zero) /\ O_opt = Some (set O1 evptrid (evptr ptrmp')) 
     \/ v' <> Vint32 (Int.zero) /\ O_opt = None) 
  end.

Definition semsignal_after_post_2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v t ptrmp ptrmp' v',
    vl = (Vint32 v) :: v' :: nil /\
    v <> Int.zero /\ 
    get O1 curtid = Some (oscurt t) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
    opv = Some (Vint32 Int.mone) /\  
    (v' = Vint32 (Int.mone) /\  O_opt = Some (set O1 evptrid (evptr ptrmp')) 
     \/ v' <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semsignal_type_bin (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e sc,
      vl = (Vint32 posv) :: nil /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (e, Int.one, sc) /\ 
        opv = None 
  end.

Definition semsignal_type_not_bin (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e tp sc, 
      vl = (Vint32 posv) :: nil /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (e, tp, sc) /\ 
        Int.eq tp Int.one = false /\ 
        opv = None 
  end.

Definition semsignal_new (vl: vallist) :=
  match vl with
    vsm :: v1 :: v2 :: v2' :: v3 :: v4 :: 
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      (semsignal_semerr (|vsm :: v1 :: nil|) ?? semsignal_sem_pos (|vsm :: v1 :: nil|));;
      (semsignal_poserr (|v1 :: v4 :: nil|)
         ??
         semsignal_get_ecb_ptr (|v1 :: v2 :: nil|);;
         (semsigna_if_null_yes (|v2 :: v4 :: nil|)
          ?? 
          semsigna_if_null_no (|v2 :: nil|);;
          partition_pos_rgn (v1 :: vr_temp_dom :: vr_temp_num ::
                                                                                  vr_temp_dom' :: vr_temp_num' :: nil)
          ((semsignal_type_bin (| v1 :: nil |);; 
            (semsignal_get_ecb_ptr1 (| v1 :: v2' :: nil |) ?? 
              semsignal_get_ecb_ptr2 (| v1 :: v2' :: nil |) ?? 
              semsignal_ecb_ptr_holder_abt (| v1 :: v2' :: nil |));;  
            (spec_code_cons 
                (sem_post_bin (v2' :: v3 :: nil)) 
                (semsignal_after_post_1 (| v3 :: v4 :: nil |) ?? semsignal_after_post_2 (| v3 :: v4 :: nil |)))
             ??
            semsignal_type_not_bin (| v1 :: nil |);; 
            (semsignal_get_ecb_ptr1 (|v1 :: v2' :: nil|) ??
             semsignal_get_ecb_ptr2 (| v1 :: v2' :: nil |) ?? 
             semsignal_ecb_ptr_holder_abt (| v1 :: v2' :: nil |));;  
            (spec_code_cons 
               (sem_post (v2' :: v3 :: nil)) 
               (semsignal_after_post_1 (|v3 :: v4 :: nil|) ?? semsignal_after_post_2 (|v3 :: v4 :: nil|))))) )) 
  | _ => spec_abort
  end.

Definition semsignalapi := (semsignal_new, (Tint32, Tptr sem_t::nil)).  


(* (****************************** sem_flush ************************************) *)

Definition semflush_iserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = nil /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semflush_semerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vsem,
      vl = vsem :: nil /\
        (vsem = Vnull \/
           exists a,
             vsem = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semflush_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition semflush_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv, 
      vl = ((Vint32 posv) :: nil) /\ 
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
      opv = Some (Vint32 (Int.mone)) /\
      O_opt = Some O1
  end.

Definition semflush_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp sc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
  end.

Definition semflush_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      (vl = Vnull  :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        O_opt = Some O1
  end. 

Definition semflush_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition semflush_get_not_hold
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e tp sc,
        vl = ((Vint32 posv) :: nil) /\ 
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          opv = None /\
          (((exists eid, e = infotid eid ) \/ e = infonull)
           /\ O_opt = Some O1
           \/
             ((~exists eid, e = infotid eid) /\ e <> infonull)
             /\ O_opt = None)
  end.

Definition semflush_type_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo eid tp sc els,
      (vl = Vint32 posv :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
         get O1 seminfoid = Some (seminfo semifo) /\
          get O1 absecblsid = Some (absecblist els) /\
         get semifo posv = Some (infotid eid, tp, sc) /\
         ~(exists n wl, get els eid = Some (abssem n, wl)) /\
(*          Int.eq tp (Int.repr OS_EVENT_TYPE_SEM) = false /\ *)
        O_opt = Some O1
  end. 

Definition semflush_get_valid_ecb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e tp sc,
        vl = ((Vint32 posv) :: nil) /\ 
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          opv = None /\
          ((exists eid, e = infotid eid ) /\ O_opt = Some O1
           \/
             ((~exists eid, e = infotid eid)/\ O_opt = None))
  end.

Definition semflush_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo tp sc,
      (vl = Vint32 posv :: nil) /\
        opv = None /\ 
         get O1 seminfoid = Some (seminfo semifo) /\
         get semifo posv = Some (infonull, tp, sc) /\
        O_opt = Some O1
  end. 

Definition semflush_no_wl
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo eid tp sc els n,
      (vl = Vint32 posv :: nil) /\
        opv = None /\ 
         get O1 seminfoid = Some (seminfo semifo) /\
          get O1 absecblsid = Some (absecblist els) /\
         get semifo posv = Some (infotid eid, tp, sc) /\
         get els eid = Some (abssem n, nil) /\
        O_opt = Some O1
  end. 

Definition semflush_set_wl_all_rdy
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo eid tp sc els n wl tls tls',
      (vl = Vint32 posv :: nil) /\
        opv = None /\ 
         get O1 seminfoid = Some (seminfo semifo) /\
         get O1 absecblsid = Some (absecblist els) /\
         get O1 abstcblsid = Some (abstcblist tls) /\
         get semifo posv = Some (infotid eid, tp, sc) /\
         get els eid = Some (abssem n, wl) /\ 
         wl <> nil /\
         tls' = set_tls_rdy wl tls /\
        O_opt = Some (set (set O1 absecblsid (absecblist (set els eid (abssem n, nil)))) abstcblsid (abstcblist tls'))
  end.

Definition semflush (vl: vallist) :=
  match vl with
    V_sem :: V_pos :: V_pevent ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil => 
      semflush_iserr (| nil |) ??
      (semflush_semerr (| V_sem :: nil |) ??
         (semflush_sem_pos (| V_sem :: V_pos :: nil |) ;;
            (semflush_poserr (| V_pos :: nil |) ??
                (semflush_get_ecb_ptr (| V_pos :: V_pevent :: nil |) ;;
                  (semflush_if_null_yes (| V_pevent :: nil |) ?? 
                    (semflush_if_null_no (| V_pevent :: nil |) ;;
                      partition_pos_rgn (V_pos :: vr_temp_dom :: vr_temp_num ::
                                                                                               vr_temp_dom' :: vr_temp_num' :: nil)
                       ((semflush_get_not_hold (| V_pos :: nil |) ;; semflush_type_err (| V_pos :: nil|)) ??
                              (semflush_get_valid_ecb (| V_pos :: nil |) ;; 
                                ((* semflush_null (| V_pos :: nil |) ?? *) semflush_no_wl (| V_pos :: nil |) ??
                                  semflush_set_wl_all_rdy (| V_pos :: nil|)) ;; isched ;; (END (Some (Vint32 Int.zero))))))))) )) 
  | _ => spec_abort
  end.

Definition semflushapi := (semflush, (Tint32, Tptr sem_t :: nil)).


(* (****************************** sem_getvalue ************************************) *)

Definition sem_getvalue_gethpnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mtp evhp t vl l,
   vl = ( (Vptr mtp) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhp) /\
  ( Get_heap evhp mtp = None \/
        (Get_heap evhp mtp = Some (mtp, t, l) /\ t <> Tint32) ) /\
   opv = None /\
   O_opt = None
end.

Definition sem_getvalue_set_sval (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists sval evhe vl l',
   vl = ( (Vptr sval) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhe) /\
   opv = None /\
   l' = Set_sval evhe sval (Vint32 Int.zero) /\
   O_opt = Some (set O1 evatomheapid (evatomheap l'))
end.

Definition sem_getvalue_semerr
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists sem pos,
    vl = sem :: pos :: nil /\
    (sem = Vnull \/
     exists a,
       sem = Vptr a /\ 
       (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
    ) /\ 
    opv = None /\
    (pos = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
     pos <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition sem_getvalue_sem_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = (Vptr a) :: v' :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition sem_getvalue_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv  ,
      vl = ((Vint32 posv)  :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
         opv = Some (Vint32 (Int.mone))
  end.

Definition sem_getvalue_svalerr
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists sval,
    vl = sval :: nil /\
    (sval = Vnull \/
     exists a,
       sval = Vptr a /\ 
       (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
    ) /\ 
    opv = Some  (Vint32 (Int.mone)) 
  end.

Definition sem_getvalue_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp sc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp, sc) /\
          (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = infotid eid) /\ e <> infonull) \/ 
                ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull))
             /\ O_opt = None)
end.
  

Definition sem_getvalue_if_null_yes    
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      (vl = Vnull :: nil) /\
        opv = Some (Vint32 (Int.mone)) 
  end. 

Definition sem_getvalue_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition sem_getvalue_sval_null_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists sval,
      (vl = sval :: nil) /\
        sval = Vnull /\
        opv = None /\
        O_opt = None
  end. 

Definition sem_getvalue_have_source (vl: vallist) (O1: osabst) (rst: option val *option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists sid n evhe l' sval,
        vl = ((Vptr sid) :: (Vptr sval) :: nil) /\
        exists els,
          opv = (Some (Vint32 Int.zero)) /\
           get O1 absecblsid = Some (absecblist els) /\
          (exists wls, get els sid = Some (abssem n, wls)) /\
          n <> Int.zero /\
          get O1 evatomheapid = Some (evatomheap evhe) /\
          l' = Set_sval evhe sval (Vint32 n)/\
          O_opt = Some (set O1 evatomheapid (evatomheap l'))
  end.

Definition sem_getvalue_no_source  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid,
        vl = ((Vptr sid) :: nil) /\
        exists els wls tcbls,
          opv = (Some (Vint32 Int.zero)) /\
           get O1 absecblsid = Some (absecblist els) /\
           get O1 abstcblsid = Some (abstcblist tcbls) /\
           get els sid = Some (abssem Int.zero, wls) /\
           (get_tls_blocked_num (TcbMod.lst tcbls) sid) = 0%nat /\
          O2 = Some O1
  end.

Definition sem_getvalue_blocked  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      exists sid sval,
        vl = ((Vptr sid) :: (Vptr sval) :: nil) /\
        exists els wls evhe l vsval tcbls l' vh,
          opv = (Some (Vint32 Int.zero)) /\
           get O1 absecblsid = Some (absecblist els) /\
           get O1 abstcblsid = Some (abstcblist tcbls) /\
           get els sid = Some (abssem Int.zero, wls) /\
           get O1 evatomheapid = Some (evatomheap evhe) /\
           Get_heap evhe sval = Some (sval, Tint32, l) /\
           l = Vint32 vh /\
           vsval = (get_tls_blocked_num (TcbMod.lst tcbls) sid) /\
           Nat.lt 0%nat vsval /\
            l' = Set_sval evhe sval (Vint32 (Int_sub_n vsval vh Int.one)) /\
          O2 = Some (set O1 evatomheapid (evatomheap l'))
  end.

Definition semgetvalue (vl:vallist) :=
  match vl with
        sem :: sval :: posv :: rv_ptr :: rv_ptr':: 
        vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil  =>
          sem_getvalue_sval_null_abt (|sval :: nil|) ??
          sem_getvalue_gethpnone_abt(|sval :: nil|) ??
          ( sem_getvalue_set_sval (|sval :: nil|) ;;
            ((sem_getvalue_semerr (|sem:: posv :: nil|)??
            sem_getvalue_sem_pos (| sem ::posv:: nil|)) ;;
               (
                 sem_getvalue_poserr (|posv :: nil|)?? 
                 sem_getvalue_svalerr (| sval :: nil |)??
                 sem_getvalue_get_ecb_ptr (|posv :: rv_ptr :: nil|);;
                 (sem_getvalue_if_null_yes (| rv_ptr :: nil|) ??
                   sem_getvalue_if_null_no (| rv_ptr :: nil|);;
                   partition_pos_rgn (posv :: vr_temp_dom :: vr_temp_num ::
                                                                                          vr_temp_dom' :: vr_temp_num' :: nil)
                    ( sem_getvalue_get_ecb_ptr (|posv :: rv_ptr' :: nil|);;
                      (sem_getvalue_if_null_yes (| rv_ptr' :: nil|) ??
                        (sem_getvalue_if_null_no (| rv_ptr' :: nil|) ;;
                          (sem_getvalue_gethpnone_abt(|sval:: nil|)??
                                (sem_getvalue_have_source(|rv_ptr'::sval::nil|) ??
                                  sem_getvalue_no_source(|rv_ptr':: nil|) ??
                                  sem_getvalue_blocked(|rv_ptr'::sval::nil|)) )) ))))))
       | _ => spec_abort
  end.

Definition semgetvalueapi := (semgetvalue, (Tint32, Tptr sem_t :: Tptr Tint32 ::nil) ). 

(* (****************************** pthread_mutexattr_init ************************************) *)

Definition mutexattr_init_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_init_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   (Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_init_set1_init (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr is_initialized (Vint32 Int.one))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_set1_proc (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr process_shared (Vint32 Int.one))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_set1_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l ct pr stt ms sus tls,
   vl = ((Vptr attr) :: nil) /\
   get O1 curtid = Some (oscurt ct) /\
   get tls ct = Some (pr, stt, ms, sus) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
      O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr prio_ceiling (Vint32 pr))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_extcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists i ptls tid,
   vl = ((Vint32 i)  :: nil) /\
     get O1 absptlsid = Some (absptls ptls) /\
     (get ptls i = Some (Valid_Addr tid) \/
     get ptls i = Some Holder) /\ 
     O_opt = Some O1
end.

Definition mutexattr_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists i ptls,
   vl = ((Vint32 i) :: nil) /\
     get O1 absptlsid = Some (absptls ptls) /\
     get ptls i = Some Null /\
     O_opt = Some O1
end.

Definition mutexattr_init_afterfor_set2_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr i evheap l t ,
   vl =  ((Vptr attr) :: (Vint32 i ) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr prio_ceiling (Vint32 i))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None)
)
end.

Definition mutexattr_for_skip (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
   opv = None /\
   O_opt = Some O1
end.

 Fixpoint mutexattr_for (V_attr: val)(n: nat) (m: nat)  :=
match n with
| 0%nat => mutexattr_for_skip(|nil|)
|S n' => (mutexattr_extcb (|(Vint32 (Int.repr (Z.of_nat m))) :: nil|) ;; mutexattr_for V_attr n' (m+1)) ??
               (mutexattr_none (|(Vint32 (Int.repr (Z.of_nat m ))) :: nil|) ;;
                    mutexattr_init_afterfor_set2_priocl(|V_attr :: (Vint32 (Int.repr (Z.of_nat m))):: nil|))
end. 

Definition mutexattr_init_afterfor_set_protocol (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr protocol (Vint32 (Int.repr PTHREAD_PRIO_INHERIT)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None)
)
end.

Definition mutexattr_init_afterfor_set_recursive (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr recursive (Vint32 (Int.repr PTHREAD_MUTEX_ERRORCHECK)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_afterfor_set_cancel_safe (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\   
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr cancel_safe (Vint32 (Int.repr PTHREAD_CANCEL_UNSAFE)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_afterfor_set_waitq_type (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   ((  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr waitq_type (Vint32 Int.zero)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattrinit_rv
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutexattrinit (vl: vallist) :=
match vl with
     (V_attr :: V_ret :: nil) => 
      mutexattr_init_attrerr (|V_attr  :: V_ret :: nil|) ??
          (mutexattr_init_set1_init (|V_attr :: nil|) ;; 
           mutexattr_init_set1_proc (|V_attr :: nil|) ;;
           mutexattr_init_set1_priocl (|V_attr :: nil|) ;; 
           mutexattr_for V_attr (64%nat)(0%nat) ;; 
           mutexattr_init_afterfor_set_protocol(|V_attr :: nil|) ;;
           mutexattr_init_afterfor_set_recursive(|V_attr :: nil|);;
           mutexattr_init_afterfor_set_cancel_safe(|V_attr :: nil|);;
           mutexattr_init_afterfor_set_waitq_type(|V_attr :: nil|);;
           mutexattrinit_rv(|V_ret :: nil|)
            )
      | _ => spec_abort
  end.

Definition mutexattrinitapi:=(mutexattrinit, (Tint32,Tptr pthread_mutexattr_t::nil)). 


(* (****************************** pthread_mutexattr_destroy ************************************) *)

Definition mutexattr_destroy_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_destroy_validptr_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_destroy_clearinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' attr evheap l vl,
   vl = ((Vptr attr) :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\    
          O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr is_initialized (Vint32 Int.zero)))) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrdestroy (vl: vallist) :=
match vl with
     (V_attr :: V_ret :: nil) => 
      mutexattr_destroy_attrerr (|V_attr  :: V_ret :: nil|) ??
      mutexattr_destroy_validptr_err (|V_attr :: nil|) ??
      mutexattr_destroy_clearinit (|V_attr :: V_ret :: nil|)
      | _ => spec_abort
  end.

Definition mutexattrdestroyapi:=(mutexattrdestroy, (Tint32,Tptr pthread_mutexattr_t::nil)).


(* (****************************** pthread_mutexattr_settype ************************************) *)

Definition mutexattr_settype_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_settype_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap e rv,
   vl = ((Vptr attr) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_settype_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_settype_muxtperr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init muxtp rv ,
    vl = ( init :: (Vint32 muxtp) :: rv :: nil) /\
    init <> Vint32 Int.zero /\
    (Int.ltu muxtp Int.zero = true \/ Int.ltu (Int.repr PTHREAD_MUTEX_DEFAULT) muxtp = true) /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_settype_getnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_settype_tp_neqdeflt_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr muxtp evheap v' vl l l',
   vl = ((Vptr attr) :: (Vint32 muxtp) :: v' :: nil) /\
   (Int.ltu Int.zero muxtp = true \/ muxtp = Int.zero ) /\ 
   Int.ltu muxtp (Int.repr PTHREAD_MUTEX_DEFAULT)  = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr recursive (Vint32 muxtp) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattr_settype_tp_eqdeflt_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr muxtp evheap v' vl l l',
   vl = ((Vptr attr) :: (Vint32 muxtp) :: v' :: nil) /\
   (Int.ltu Int.zero muxtp = true \/ muxtp = Int.zero ) /\ 
   muxtp = (Int.repr PTHREAD_MUTEX_DEFAULT) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr recursive (Vint32 (Int.repr PTHREAD_MUTEX_ERRORCHECK)) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrsettype (vl: vallist) :=
match vl with
     (V_attr :: V_muxtp :: V_init :: V_ret :: nil) => 
       mutexattr_settype_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_settype_getnone_abt (|V_attr :: nil|) ??
      ( mutexattr_settype_getinit (|V_attr :: V_init :: nil|) ;; 
      ( mutexattr_settype_init_zero_eq (|V_init :: V_ret :: nil|)  ??
        mutexattr_settype_muxtperr (| V_init :: V_muxtp :: V_ret :: nil|) ?? 
       mutexattr_settype_getnone_abt (|V_attr :: nil|) ??
        mutexattr_settype_tp_neqdeflt_set_recv (|V_attr :: V_muxtp :: V_ret :: nil|) ??
        mutexattr_settype_tp_eqdeflt_set_recv (|V_attr :: V_muxtp :: V_ret :: nil|)))
      | _ => spec_abort
  end.

(* added missing parameter type *) 
Definition mutexattrsettypeapi:=(mutexattrsettype, (Tint32,Tptr pthread_mutexattr_t::Tint32::nil)).


(* (****************************** pthread_mutexattr_gettype ************************************) *)

Definition mutexattr_gettype_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_gettype_mtperr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr mtp v',
      vl = ((Vptr attr) :: mtp :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
        (mtp = Vnull \/
           exists a,
             mtp = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.


Definition mutexattr_gettype_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp evheap e rv,
   vl = ((Vptr attr) :: (Vptr mtp) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart mtp = true /\
   cmpaddr Cle mtp userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_gettype_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_gettype_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp evheap t vl l,
   vl = ((Vptr attr) :: (Vptr mtp) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart mtp = true /\
   cmpaddr Cle mtp userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_gettype_gethpnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mtp evhp t vl l,
   vl = ( (Vptr mtp) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhp) /\
  (Get_heap evhp mtp = None \/
        (Get_heap evhp mtp = Some (mtp, t, l) /\ t <> Tint32) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_gettype_tp_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp mattrheap recv evhe v' vl l',
   vl = ((Vptr attr) :: (Vptr mtp) :: v' :: nil) /\
   get O1 evstructheapid = Some (evstructheap mattrheap) /\
   Some recv = Get_structe mattrheap attr recursive /\
   get O1 evatomheapid = Some (evatomheap evhe) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_sval evhe mtp recv/\
       O_opt = Some (set O1 evatomheapid (evatomheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrgettype (vl: vallist) :=
match vl with
     (V_attr :: V_mtp :: V_init :: V_ret :: nil) => 
       mutexattr_gettype_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_gettype_mtperr (|V_attr :: V_mtp  :: V_ret :: nil|) ??
       mutexattr_gettype_getstruct_none_abt (|V_attr :: V_mtp :: nil|) ??
      ( mutexattr_gettype_getinit (|V_attr :: V_mtp :: V_init :: nil|) ;; 
      ( mutexattr_gettype_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_gettype_getstruct_none_abt (|V_attr :: V_mtp :: nil|) ??
         mutexattr_gettype_gethpnone_abt (| V_mtp :: nil|) ??
         mutexattr_gettype_tp_set_recv (|V_attr :: V_mtp :: V_ret :: nil|) ))
      | _ => spec_abort
  end.

(* added missing parameter type *) 
Definition mutexattrgettypeapi:=(mutexattrgettype, (Tint32,Tptr pthread_mutexattr_t::Tptr Tint32::nil)).


(* (****************************** pthread_mutexattr_setprioceiling ************************************) *)

Definition mutexattr_setprioceiling_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_setprioceiling_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap e rv,
   vl = ((Vptr attr) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_priocl_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists priocl rv,
   vl = ( Vint32 priocl :: rv ::nil) /\
  (Int.ltu priocl Int.zero = true \/
    Int.ltu (Int.repr OS_MAX_TASKS) priocl = true )/\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_setprioceiling_getstruct_none_pc_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap t vl l,
   vl = ((Vptr attr) :: (Vint32 pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   Int.ltu pc Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) pc = false /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_setprioceiling_extcb_priocl_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists priocl ptls tid rv,
   vl = ((Vint32 priocl) :: rv :: nil) /\
   Int.ltu priocl Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false /\
     get O1 absptlsid = Some (absptls ptls) /\
     (get ptls priocl = Some (Valid_Addr tid) \/
     get ptls priocl = Some Holder) /\ 
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_none_setpriocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr priocl evheap ptls l v' l',
   vl = ((Vptr attr )::(Vint32 priocl) :: v' :: nil) /\
   Int.ltu priocl Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false /\
     get O1 absptlsid = Some (absptls ptls) /\
     get ptls priocl = Some Null /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr prio_ceiling (Vint32 priocl) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrsetprioceiling (vl: vallist) :=
match vl with
     (V_attr :: V_priocl :: V_init :: V_ret :: nil) => 
       mutexattr_setprioceiling_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_setprioceiling_getstruct_none_abt (|V_attr :: nil|) ??
      ( mutexattr_setprioceiling_getinit (|V_attr :: V_init :: nil|) ;; 
      ( mutexattr_setprioceiling_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_setprioceiling_priocl_err (| V_priocl :: V_ret :: nil|) ??
         mutexattr_setprioceiling_getstruct_none_pc_abt (|V_attr :: V_priocl :: nil|) ??
         mutexattr_setprioceiling_extcb_priocl_err (| V_priocl :: V_ret :: nil|)??
         mutexattr_setprioceiling_none_setpriocl (|V_attr :: V_priocl :: V_ret :: nil|) ))
      | _ => spec_abort
  end.

(* added missing parameter type *) 
Definition mutexattrsetprioceilingapi:=(mutexattrsetprioceiling, (Tint32,Tptr pthread_mutexattr_t::Tint32::nil)).


(* (****************************** pthread_mutexattr_getprioceiling ************************************) *) 

Definition mutexattr_getprioceiling_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_getprioceiling_mtperr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr pc v',
      vl = ((Vptr attr) :: pc :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
        (pc = Vnull \/
           exists a,
             pc = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.


Definition mutexattr_getprioceiling_getinit_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap,
   vl = ((Vptr attr) :: (Vptr pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   None = Get_structe evheap attr is_initialized /\
    opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap e rv,
   vl = ((Vptr attr) :: (Vptr pc) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_getprioceiling_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_getprioceiling_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap t vl l,
   vl = ((Vptr attr) :: (Vptr pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_gethpnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pc evhp t vl l,
   vl = ( (Vptr pc) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhp) /\
  ( Get_heap evhp pc = None \/
        (Get_heap evhp pc = Some (pc, t, l) /\ t <> Tint32) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_tp_set_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc mattrheap priocl evhe v' vl l',
   vl = ((Vptr attr) :: (Vptr pc) :: v' :: nil) /\
   get O1 evstructheapid = Some (evstructheap mattrheap) /\
   Some priocl = Get_structe mattrheap attr prio_ceiling /\
   get O1 evatomheapid = Some (evatomheap evhe) /\
   opv = Some (Vint32 (Int.repr 0)) /\ 
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_sval evhe pc priocl/\
       O_opt = Some (set O1 evatomheapid (evatomheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrgetprioceiling (vl: vallist) :=
match vl with
     (V_attr :: V_priocl :: V_init :: V_ret :: nil) => 
       mutexattr_getprioceiling_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_getprioceiling_mtperr (|V_attr :: V_priocl  :: V_ret :: nil|) ??
       mutexattr_getprioceiling_getstruct_none_abt (|V_attr :: V_priocl :: nil|) ??
      ( mutexattr_getprioceiling_getinit (|V_attr :: V_priocl :: V_init :: nil|) ;; 
      ( mutexattr_getprioceiling_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_getprioceiling_getstruct_none_abt (|V_attr :: V_priocl :: nil|) ??
         mutexattr_getprioceiling_gethpnone_abt (| V_priocl :: nil|) ??
         mutexattr_getprioceiling_tp_set_priocl (|V_attr :: V_priocl :: V_ret :: nil|) ))
      | _ => spec_abort
end.

(* added missing parameter type *) 
Definition mutexattrgetprioceilingapi:=(mutexattrgetprioceiling, (Tint32,Tptr pthread_mutexattr_t::Tptr Tint32::nil)).


(* (****************************** pthread_mutex_trylock ************************************) *)

Definition mutextrylock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutextrylock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = ((Vptr a) :: v' :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition mutextrylock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextrylock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pro pi,
          exists c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
          (((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
             /\ O_opt = None)
  end.

Definition mutextrylock_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((v' = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end. 

Definition mutextrylock_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = (Vptr eid) :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mutextrylock_if_null_owner_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n w pro c, 
        exists mc pi qls pr y wl rv,
        vl =((Vint32 posv) :: (Vptr eid) :: rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls eid =Some (absmutexsem pr y, wl) /\
        (( y = None /\ ow = $ OS_MUTEX_AVAILABLE )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
          opv = None /\
          ( (rv = (Vint32 ow) /\ O_opt = Some O1) \/
           (rv <> (Vint32 ow) /\O_opt = None) )
  end. 

Definition mutextrylock_recurtype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pro,
        exists pi c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
        opv =None /\
        (( v' = Vint32 x /\ O_opt = Some O1) \/
        ( v' <> Vint32 x /\ O_opt = None ))
  end.

Definition mutextrylock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists curp t prio st m sus tls, 
          vl = ( curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( curp = Vint32 prio /\ O_opt = Some O1) \/
          ( curp <> Vint32 prio /\ O_opt = None ))
  end. 

Definition mutextrylock_prioceil
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv v' mls e o x n w pi pro,
        exists c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c,mc) /\
        opv = None /\
        (( v' = Vint32 pi /\ O_opt = Some O1) \/
        ( v' <> Vint32 pi /\ O_opt = None ))
  end.

Definition mutextrylock_get_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x ,
        exists pi n w pro c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
        opv = None /\
        (( v' = Vint32 n /\ O_opt = Some O1) \/
        ( v' <> Vint32 n /\ O_opt = None ))
  end.

Definition mutextrylock_if_lt_cnt_max_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists n rv posv tp ty ow curp mls o w , 
      exists pi priocl pro pe c mc eid cn,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, ty, cn, pro, pi, w, c, mc) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        ( ow = curp \/ priocl = curp ) /\
        Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) =false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutextrylock_if_lt_cnt_max_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists n rv posv tp ty curp mls eid o w, 
      exists pi priocl ow pe c mc pro cn,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) ::  rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, ty, cn, pro, pi, w, c, mc) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        ( ow = curp \/ priocl = curp ) /\
        Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) = true /\
        opv = Some (Vint32 (Int.repr 0)) /\
        ((rv = (Vint32 (Int.repr 0)) /\
                O_opt = Some (set O1 absmutinfoid
                              (absmutinfo (set mls posv (pe, o, ty, (Int.add cn Int.one), pro, pi, w, c, mc))))
           )
           \/ (rv <> Vint32 (Int.repr 0) /\ O_opt = None))
  end.

Definition mutextrylock_after_acc_1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv eid ,
      vl = ((Vint32 posv) :: (Vint32 v') :: (Vptr eid) :: nil) /\
        exists ow o x n w pro c mc,
         exists pi wl p els mls eid ,
        Int.eq (Int.repr 1) v' = true /\
        get O1 absecblsid = Some (absecblist els) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) /\
        get els eid = Some (absmutexsem p ow,wl) /\  
        opv = None /\
         O_opt = Some (set O1 absmutinfoid (absmutinfo (
          set mls posv (Valid_Addr eid, ow, x, n, pro, pi, w, c, mc))))
  end.

Definition mutextrylock_afteracc1_rv
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutextrylock_if_null_yes_afteracc
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutextrylock_after_acc_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.eq (Int.repr 1) v = false /\ 
        opv = Some (Vint32 (Int.repr EBUSY)) /\
        (v' = Vint32 (Int.repr EBUSY) /\ O_opt = Some O1 
         \/ v' <> Vint32 (Int.repr EBUSY) /\ O_opt = None)
  end. 

Definition mutextrylock_get_ecb_ptr1 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c mc ptrmp t, 
    vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Null, o, x, n, pro, pi, w, c, mc) /\
    get O1 evptrid = Some (evptr ptrmp) /\ 
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition mutextrylock_get_ecb_ptr2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c mc ptrmp t eid, 
    vl = ((Vint32 posv) :: v' :: nil) /\
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t ( Vptr eid, Vnull, Vnull)))) \/ 
     v' <> Vptr eid /\ O_opt = None)
  end.

Definition mutextrylock_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists posv mls o x n pro pi w c mc, 
    vl = ((Vint32 posv) :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Holder, o, x, n, pro, pi, w, c, mc) /\
    O_opt = None 
  end.

Definition mutextrylock_after_acc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists t ptrmp ptrmp',
      vl = nil /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        opv = None /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end. 

Definition callacc (V_pos:val)(V_pevt:val)(V_eid0:val)(V_accrv:val)(V_ret:val) :=
                                               (mutextrylock_get_ecb_ptr1 (|V_pos:: V_pevt :: nil|)??
                                                mutextrylock_get_ecb_ptr2 (|V_pos:: V_pevt :: nil|)??
                                                mutextrylock_ecb_ptr_holder_abt(|V_pos :: nil|)) ;;
                                                            mutexacc (V_pevt :: V_accrv::nil);; mutextrylock_after_acc_ptr (|nil|) ;;
                                                     ((mutextrylock_ecb_ptr (|V_pos :: V_eid0 :: nil|);;
                                                      (mutextrylock_if_null_yes_afteracc(|V_eid0 :: V_ret :: nil|) ??
                                                        ( mutextrylock_after_acc_1 (|V_pos ::V_accrv :: V_eid0 :: nil|);; mutextrylock_afteracc1_rv (| V_ret :: nil|))))  ??
                                                      mutextrylock_after_acc_2 (|V_accrv ::V_ret::nil|)).

Definition mutextrylock (vl: vallist) :=
match vl with
    (V_mux :: V_pos :: V_eid :: V_eid' :: V_ow :: V_tp :: V_curp :: V_priocl :: V_pevt :: V_recurcnt :: V_eid0 :: V_accrv :: V_ret ::
      vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil)=>
                  (mutextrylock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutextrylock_mutex_pos(|V_mux :: V_pos :: nil|));;
                      (mutextrylock_poserr (|V_pos :: V_ret :: nil|) ?? 
                         (mutextrylock_ecb_ptr (|V_pos :: V_eid :: nil|);; 
                            (mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutextrylock_if_null_no (|V_eid :: nil|) ;;
                                mutextrylock_ecb_ptr (|V_pos :: V_eid' :: nil|) ;;
                                (mutextrylock_if_null_yes (|V_eid' :: V_ret :: nil|) ??
                                   (mutextrylock_if_null_owner_no (|V_pos :: V_eid' :: V_ow :: nil|) ;;
                                     partition_pos_rgn (V_pos :: vr_temp_dom :: vr_temp_num ::
                                                                                                            vr_temp_dom' :: vr_temp_num' :: nil)
                                        (mutextrylock_recurtype(|V_pos :: V_tp :: nil|) ;; 
                                        ( (
                                             mutextrylock_curprio(| V_curp :: nil|) ;; mutextrylock_prioceil(|V_pos :: V_priocl :: nil|) ;;
                                               ( 
                                                      (mutextrylock_get_recurcnt (| V_pos :: V_recurcnt :: nil|) ;;
                                                         (mutextrylock_if_lt_cnt_max_yes (|V_pos :: V_eid' :: V_ow ::  V_tp :: V_curp :: V_priocl :: V_recurcnt :: V_ret :: nil|) ??
                                                          mutextrylock_if_lt_cnt_max_no (|V_pos :: V_eid' :: V_ow ::  V_tp :: V_curp :: V_priocl :: V_recurcnt :: V_ret :: nil|))) ?? 
                                                          (callacc V_pos V_pevt V_eid0 V_accrv V_ret)
                                               )
                                           ) ??
                                                (callacc V_pos V_pevt V_eid0 V_accrv V_ret)
                                          )) ))))))
  | _ => spec_abort
  end.

Definition mutextrylockapi:=(mutextrylock, (Tint32,Tptr pthread_mutex_t::nil)).


(* (****************************** pthread_mutex_init ************************************) *)

(* from os_inv.v *) 
Definition V_muxattr_prioceiling (vl:vallist) := nth_val 2 vl.
Definition V_muxattr_cancelsafe      (vl:vallist) := nth_val 6 vl.

Definition mutex_init_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vmux,
      vl = vmux :: nil /\
        (vmux = Vnull \/
           exists a,
             vmux = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O_opt = Some O1
  end.

Definition mutex_init_attr_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = Vnull :: nil /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutex_init_attr_no_free
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists rv_attr,
      vl = Vint32 rv_attr :: nil /\
      Int.eq rv_attr Int.zero = false /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O_opt = Some O1
  end.

Definition mutex_init_attr_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
(*      exists vattr ventity , *)
      vl = (* vattr :: ventity :: *) Vint32 Int.zero :: nil /\
(*       vattr = ventity /\ *)
      opv = None /\
      O_opt = Some O1
  end.

Definition mutex_init_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv muxinfo cpn idx left right, 
      vl = (posv :: Vint32 idx :: Vint32 cpn :: nil) /\
       get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
       left = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx)%Z /\
       right = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1))%Z /\
      (
      ((~(exists pos ow tp rcnt prot prioc wq cnsa mc,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
                       (left <= (Int.unsigned pos) < right)%Z) /\
          posv = Vint32 (Int.repr 255)) \/
       (exists pos ow tp rcnt prot prioc wq cnsa mc,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\
         posv = Vint32 pos )) /\ O_opt = Some O1
      ) \/
      (
      ((~(exists pos ow tp rcnt prot prioc wq cnsa mc,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
                       (left <= (Int.unsigned pos)  < right)%Z) /\
      posv <> Vint32 (Int.repr 255)) \/
     (exists pos ow tp rcnt prot prioc wq cnsa mc,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\
      posv <> Vint32 pos )) /\ O_opt = None
      )
end.

Definition mutex_init_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos, 
      vl = ((Vint32 pos) :: nil) /\ 
      Int.eq pos (Int.repr 255) = true /\
      opv = Some (Vint32 (Int.repr EAGAIN)) /\
      O_opt = Some O1
  end.

(* set ECB pointer in EIB to the placeholder *)
(* update the ghost location and index to reflect the status of creating a mux. *) 
Definition mutex_init_set_placeholder
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos muxinfo muxinfo',
    exists e ow tp rcnt prot prioc wq cnsa mc,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos =  Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)  /\
      muxinfo' = set muxinfo pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\
      opv = None /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo'))
  end.

Definition mutex_init_attr_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists attr evheap t vl l,
      vl = ((Vptr attr) :: nil) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      ( Get_struct evheap attr = None \/
            (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
       opv = None /\
       O_opt = None
  end.

Definition mutex_init_get_attr_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr prioc evheap attr_vl pip,
      vl = (Vptr attr :: prioc :: nil) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_prioceiling attr_vl = Some (Vint32 pip) /\
      (0 <= Int.unsigned pip < 64)%Z /\
      opv = None /\
      ( prioc = Vint32 pip /\ O_opt = Some O1
         \/ (prioc <> Vint32 pip)/\ O_opt = None)
  end.

Definition mutex_init_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t muxinfo muxinfo',
    exists e ow tp rcnt prot prioc wq cnsa mc,
    exists locmp locmp' ptrmp ptrmp' muxp semp qp,
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\
      get O1 curtid = Some (oscurt t) /\
      get O1 evlocid = Some (evloc locmp) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\
      get O1 evptrid = Some (evptr ptrmp) /\
      get ptrmp t = Some (muxp, semp, qp) /\
      ptrmp' = set ptrmp t (Vnull, semp, qp) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr 
                        /\ muxinfo' = set muxinfo pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc))) 
        \/ eptr = Vnull /\ muxinfo' = set muxinfo pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) /\  
       O_opt = Some (set (set (set O1 absmutinfoid (absmutinfo muxinfo')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
  end.

Definition mutex_init_holder_abt
           (vl: vallist) (O: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = Vptr vhold_addr :: nil /\ O_opt = None
  end.   

Definition mutex_init_err_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        (((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutex_init_get_verr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists errid rv_verr ebls ed,
      vl = (Vptr errid :: rv_verr :: nil) /\
      get O1 eblsid = Some (eblist ebls) /\
      get ebls errid = Some ed /\
      opv = None /\
      ( rv_verr = Vint32 ed /\ O_opt = Some O1
         \/ rv_verr <> Vint32 ed /\ O_opt = None)
  end.

Definition mutex_init_create_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos err, 
    vl = (Vint32 pos :: Vint32 err :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    Int.eq err (Int.repr OS_NO_ERR) = false /\
    opv = Some (Vint32 (Int.repr EAGAIN)) /\
    O_opt = Some O1 
  end.

Definition mutex_init_create_succ
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos, 
    vl = (Vint32 pos :: Vint32 (Int.repr OS_NO_ERR) :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    opv = None /\
    O_opt = Some O1 
  end.

Definition mutex_init_set_cancel
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa cnsa' mc, 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_cancelsafe attr_vl = Some (Vint32 cnsa') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq, cnsa', mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_protocol
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa mc prot', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_protocol attr_vl = Some (Vint32 prot') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot', prioc, wq, cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_recursive
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos muxinfo muxinfo',
      exists e ow tp rcnt prot prioc wq cnsa mc, 
      vl = (Vint32 pos) :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, Int.zero, prot, prioc, wq, cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos muxinfo muxinfo',
      exists e ow tp rcnt prot prioc wq cnsa mc, 
      vl = (Vint32 pos) :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      MibMod.get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      opv = None /\
      muxinfo' = set muxinfo pos (e, None, tp, rcnt, prot, prioc, wq, cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa mc prioc', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_prioceiling attr_vl = Some (Vint32 prioc') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc', wq, cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa mc rec, 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_recursive attr_vl = Some (Vint32 rec) /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, rec, rcnt, prot, prioc, wq, cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_waitq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa mc wq', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_waitq attr_vl = Some (Vint32 wq') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq', cnsa, mc) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_mux
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a pos pbls,
      vl = (Vptr a) :: (Vint32 pos) :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = Some (Vint32 (Int.zero)) /\
        (((exists posv, get pbls a = Some posv) /\ O_opt = Some (set O1 pblsid (pblist (set pbls a pos))))
          \/ ~(exists posv, get pbls a = Some posv) /\ O_opt = None)
  end.

Definition mutex_init_after_get_attr (vl: vallist) :=
  match vl with
    vmux :: vattr :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: vr_temp_dom :: vr_temp_num :: nil => 
    (kscurdom_ext (| nil |) ;;
     get_temp_dom (| vr_temp_dom :: nil |) ;;
     get_temp_num (| vr_temp_num :: nil |) ;;
     mutex_init_pos (| posv :: vr_temp_dom :: vr_temp_num :: nil |);;
         (mutex_init_poserr (|posv :: nil|) ??
            (mutex_init_set_placeholder (|posv :: nil|) ;; 
              (mutex_init_attr_none (| vattr :: nil |) ??
                mutex_init_get_attr_prioceiling (| vattr :: rv_prioc :: nil |)) ;;
             mutexcre (rv_prioc :: verr :: rv_cre :: nil) ;;
             (mutex_init_set_ecb_ptr (| posv :: rv_cre :: nil |) ?? mutex_init_holder_abt (| rv_cre :: nil|));;  
             ( mutex_init_err_none (| verr :: nil |) ??
                mutex_init_get_verr (| verr :: rv_verr :: nil |) ;;
                (mutex_init_create_err (| posv :: rv_verr :: nil |) ?? 
                  mutex_init_create_succ (| posv :: rv_verr :: nil |) ;;
               ( (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_cancel (| posv :: vattr :: nil |)) ;;
                  (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_protocol (| posv :: vattr :: nil |)) ;;
                  mutex_init_set_recursive (| posv :: nil |) ;;
                  mutex_init_set_owner (| posv :: nil |) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_prioceiling (| posv :: vattr :: nil |)) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_type (| posv :: vattr :: nil |)) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_waitq (| posv :: vattr :: nil |)) ;;
                 mutex_init_set_mux (| vmux :: posv :: nil |)))) )))
   | _ => spec_abort
   end.

Definition mutex_init (vl: vallist) :=
  match vl with
    vmux :: vattr :: ventity :: verr :: rv_attr :: posv :: rv_prioc :: rv_cre :: rv_verr :: 
    vr_temp_dom :: vr_temp_num :: nil => 
      mutex_init_muxerr (| vmux :: nil |) ??
      (mutex_init_attr_null (| vattr :: nil |) ;; 
                mutexattrinit (ventity :: rv_attr :: nil ) ;;
                     (mutex_init_attr_no_free (| rv_attr :: nil |) ??
                        (mutex_init_attr_succ (| (* vattr :: ventity :: *) rv_attr :: nil |) ;;
                            mutex_init_after_get_attr (vmux :: ventity :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: vr_temp_dom :: vr_temp_num :: nil)  ) )) ??
       mutex_init_after_get_attr (vmux :: vattr :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: vr_temp_dom :: vr_temp_num :: nil)
  | _ => spec_abort
  end.

(* pthread_mutex_info_t -> pthread_mutex_t *) 
Definition mutexinitapi := (mutex_init, (Tint32, Tptr pthread_mutex_t :: Tptr pthread_mutexattr_t :: Tptr pthread_mutexattr_t :: Tptr Int8u :: nil)). 


(* (****************************** pthread_mutex_destroy ************************************) *)

Definition mutex_destroy_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
      vl = v :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
         O_opt = Some O1
  end.

Definition mutex_destroy_mux_nopblk_abt
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a',
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = None /\ 
      O_opt = None
  end.

Definition mutex_destroy_pos_err 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\
      (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ Int.eq posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\ 
      opv = Some (Vint32 (Int.repr EINVAL)) /\ 
     O_opt = Some O1
  end.

Definition mutex_destroy_pevent_null_err
    (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.repr EINVAL)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
      exists muxeibs ow tp rcnt prot prioc wq cnsa mc,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        O_opt = Some O1 
  end.

Definition mutex_destroy_not_placeholder_assm
    (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\   
     exists muxeibs ow tp rcnt prot prioc wq cnsa mc,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        O_opt = None
  end.

Definition mutex_destroy_waiting_tasks_err
    (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.repr EBUSY)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\   
     exists muxeibs ow tp rcnt prot prioc wq cnsa mc,
     exists eid els pip o wls,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, wls) /\
        wls <> nil /\
        O_opt = Some O1
  end.

Definition mutex_destroy_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
       exists v,
        vl = (v :: nil) /\
        opv = Some (Vint32 (Int.repr EBUSY)) /\ 
         O_opt = Some O1
  end.

Definition mutex_destroy_pip_err (vl: vallist) (O1: osabst) (rst: option val *option osabst) := 
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.zero)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
     exists muxeibs ow tp rcnt prot prioc wq cnsa mc,
     exists eid els pip o ptls,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        ~(get ptls pip = Some Holder) /\
       O_opt = None
  end.

Definition mutex_destroy_succ (vl: vallist) (O1: osabst) (rst: option val *option osabst) := 
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.zero)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\    
     exists muxeibs ow tp rcnt prot prioc wq cnsa mc,
     exists eid els pip o els' muxeibs' ptls ptls',
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls pip = Some Holder /\
        ptls' = set ptls pip Null /\
        join els' (sig eid (absmutexsem pip o, nil)) els /\
        muxeibs' = set muxeibs posv (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) /\ 
        O_opt = Some (set (set (set O1 absecblsid (absecblist els')) absmutinfoid (absmutinfo muxeibs')) absptlsid (absptls ptls'))
  end. 

Definition mutex_destroy (vl: vallist) :=
  match vl with
    vmux :: nil => 
      mutex_destroy_muxerr (| vl |) ??
      mutex_destroy_mux_nopblk_abt (| vl |) ?? 
      mutex_destroy_pos_err (| vl |) ??
      mutex_destroy_not_placeholder_assm (| vl |) ??
      mutex_destroy_pevent_null_err (| vl |) ??
      (kscurdom_ext (| nil |) ;; partition_pos_out_of_rgn_err (| vl |)) ??
      mutex_destroy_waiting_tasks_err (| vl |) ??
      mutex_destroy_iserr (| vl |) ??
      mutex_destroy_pip_err (| vl |) ??
      mutex_destroy_succ (| vl |)
  | _ => spec_abort 
 end.

(* pthread_mutex_info_t -> pthread_mutex_t *) 
Definition pthread_mutex_destroy_api := (mutex_destroy, (Tint32, Tptr pthread_mutex_t :: nil)).


(* (****************************** pthread_mutex_lock ************************************) *)

Definition mutexlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v_pos,
      vl = (v :: v_pos :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v_pos = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v_pos <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutexlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v_pos pbls,
      vl = ((Vptr a) :: v_pos :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = None /\
        ((exists posv,
               (get pbls a = Some posv /\
                  (v_pos = (Vint32 posv) /\ O_opt = Some O1 \/ v_pos <> (Vint32 posv) /\ O_opt = None)))
          \/ get pbls a = None /\ O_opt = None)
  end.

Definition mutexlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutexlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_pevent :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        (((exists eid, e = Valid_Addr eid /\ v_pevent = Vptr eid) \/ e = Null /\ v_pevent = Vnull)
           /\ O_opt = Some O1
           \/
             (e = Holder \/ 
                (exists eid, e = Valid_Addr eid /\ v_pevent <> Vptr eid) \/ (e = Null /\ v_pevent <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutexlock_ecb_nullerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv,
      (vl = Vnull :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end.

Definition mutexlock_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n pro w c, 
        exists mc pcp qls pr y wl v_ow,
      vl =((Vint32 posv) :: (Vptr eid) :: v_ow :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
      get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls eid =Some (absmutexsem pr y, wl) /\
      opv = None /\
      ((ow = $ OS_MUTEX_AVAILABLE /\ y = None )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
      ( (v_ow = (Vint32 ow) /\ O_opt = Some O1) \/
          (v_ow <> (Vint32 ow) /\O_opt = None))
  end.

Definition mutexlock_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_tp posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_tp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
        (( v_tp = Vint32 x /\ O_opt = Some O1) \/
          ( v_tp <> Vint32 x /\ O_opt = None ))
  end.

Definition mutexlock_typeerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp, 
        vl = ((Vint32 tp) :: rv :: nil) /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false /\
        opv = Some (Vint32(Int.repr EINVAL)) /\
        ((rv = (Vint32(Int.repr EINVAL)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EINVAL)) /\ O_opt = None))
  end.

Definition mutexlock_type_normal
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tp, 
        vl = ((Vint32 tp) :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_NORMAL) /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutexlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_curp t prio st m sus tls, 
          vl = ( v_curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( v_curp = Vint32 prio /\ O_opt = Some O1) \/
          ( v_curp <> Vint32 prio /\ O_opt = None ))
  end.

Definition mutexlock_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pcp posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_pcp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
        (( v_pcp = Vint32 pcp /\ O_opt = Some O1) \/
          ( v_pcp <> Vint32 pcp /\ O_opt = None ))
  end.

Definition mutexlock_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_rcnt posv mls e o x ,
        exists n pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_rcnt :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
          (( v_rcnt = Vint32 n /\ O_opt = Some O1) \/
          ( v_rcnt <> Vint32 n /\ O_opt = None ))
  end.

Definition mutexlock_type_deadlk
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_ERRORCHECK) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        opv = Some (Vint32(Int.repr EDEADLK)) /\
        ((rv = (Vint32(Int.repr EDEADLK)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EDEADLK)) /\ O_opt = None))
  end.

Definition mutexlock_type_recur_again
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp rcnt, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutexlock_type_recur_incre_one
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv tp ow curp pcp rcnt, 
      exists mls e o x cn pro pip w c mc,
        vl = ((Vint32 posv) :: (Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, cn, pro, pip, w, c, mc) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\
           O_opt = Some (set O1 absmutinfoid 
                                      (absmutinfo (set mls posv (e, o, x, (Int.add cn Int.one), pro, pip, w, c, mc))))) \/
        (rv <> (Vint32 Int.zero) /\ O_opt = None))
  end.

Definition mutexlock_after_pend_fail
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_NO_ERR) = false /\
        opv = Some(Vint32 (Int.repr EINVAL)) /\
        (( rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None ))
  end.

Definition mutexlock_after_pend_succ_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: Vnull :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        (( rv = Vint32 Int.zero /\ O_opt = Some O1) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutexlock_after_pend_succ_ecb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr eid posv rv,
      exists mls o x n pro pcp w c mc,
      exists els p ow wl,
        vl = ((Vint32 verr) :: (Vptr eid) :: (Vint32 posv) :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem p ow,wl) /\
        (( rv = Vint32 Int.zero 
            /\ O_opt = Some (set O1 absmutinfoid 
                                            (absmutinfo (set mls posv (Valid_Addr eid, ow, x, n, pro, pcp, w, c, mc))))) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutexlock_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (v_pevent, Vnull, Vnull))))
  end.


Definition mutexlock (vl: vallist) :=
match vl with
    (V_mux :: V_pos :: V_eid0 :: V_eid :: V_ow :: V_tp :: V_curp :: V_pcp :: V_rcnt ::  V_pevt :: V_err :: V_afteid :: V_ret ::
      vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' ::  nil)=>
             (mutexlock_muxerr (| V_mux :: V_pos :: nil |) ??
               mutexlock_mutex_pos (| V_mux :: V_pos :: nil |)) ;;
             (mutexlock_poserr (| V_pos :: V_ret :: nil |) ??
               (mutexlock_ecb_ptr (| V_pos :: V_eid0 :: nil |) ;;
                    (mutexlock_ecb_nullerr (| V_eid0 :: V_ret :: nil |) ??
                       partition_pos_rgn (V_pos :: vr_temp_dom :: vr_temp_num ::
                                                             vr_temp_dom' :: vr_temp_num' :: nil)
                        (mutexlock_ecb_ptr (| V_pos :: V_eid :: nil |) ;;
                          (mutexlock_ecb_nullerr (| V_eid :: V_ret :: nil |) ??
                            mutexlock_owner (| V_pos :: V_eid :: V_ow :: nil |) ;;
                            mutexlock_type (| V_pos :: V_tp :: nil |) ;;
                                (mutexlock_typeerr (| V_tp :: V_ret :: nil |) ??
                                    (mutexlock_curprio (| V_curp :: nil |) ;;
                                     mutexlock_prioceiling (| V_pos :: V_pcp :: nil |) ;;
                                      (mutexlock_type_deadlk (| V_tp :: V_ow :: V_curp :: V_pcp :: V_ret :: nil |) ??
                                        (mutexlock_recurcnt (| V_pos :: V_rcnt :: nil |) ;;
                                                (mutexlock_type_recur_incre_one (| V_pos :: V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |) ??
                                                  mutexlock_type_recur_again (| V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |))) ??
                                        (mutexlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                                          mutexlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                                          spec_code_cons (mutexpend (V_pevt :: (Vint32 Int.zero) :: V_err :: nil))
                                          ( mutexlock_set_evloc_ptr (| Vnull :: nil |) ;;
                                           (mutexlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                                              (mutexlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                                                  (mutexlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                                                    mutexlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) ) ??
                              ( mutexlock_type_normal (| V_tp :: nil |) ;;
                                    mutexlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                                       mutexlock_set_evloc_ptr (| V_pevt :: nil |) ;; 
                                          spec_code_cons (mutexpend (V_pevt :: (Vint32 Int.zero) :: V_err :: nil))
                                          ( mutexlock_set_evloc_ptr (| Vnull :: nil |) ;;
                                             (mutexlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                                              (mutexlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                                                  (mutexlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                                                    mutexlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) )))))
  | _ => spec_abort
  end.

Definition mutexlockapi:=(mutexlock, (Tint32,Tptr pthread_mutex_t::nil)).


(* (****************************** pthread_mutex_timedlock ************************************) *)

Definition mutextimedlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v_pos,
      vl = (v :: v_pos :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v_pos = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v_pos <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutextimedlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v_pos pbls,
      vl = ((Vptr a) :: v_pos :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = None /\
        ((exists posv,
               (get pbls a = Some posv /\
                  (v_pos = (Vint32 posv) /\ O_opt = Some O1 \/ v_pos <> (Vint32 posv) /\ O_opt = None)))
          \/ get pbls a = None /\ O_opt = None)
  end.

Definition mutextimedlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextimedlock_timeout_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tmv rv ,
      vl = ((Vint32 tmv) :: rv :: nil) /\
        (Int.eq tmv Int.zero = true \/
           Int.ltu (Int.repr 65535) tmv = true) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextimedlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_pevent :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        (((exists eid, e = Valid_Addr eid /\ v_pevent = Vptr eid) \/ e = Null /\ v_pevent = Vnull)
           /\ O_opt = Some O1
           \/
             (e = Holder \/ 
                (exists eid, e = Valid_Addr eid /\ v_pevent <> Vptr eid) \/ (e = Null /\ v_pevent <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutextimedlock_ecb_nullerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv,
      (vl = Vnull :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end.

Definition mutextimedlock_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n pro w c, 
        exists mc pcp qls pr y wl v_ow,
      vl =((Vint32 posv) :: (Vptr eid) :: v_ow :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
      get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls eid =Some (absmutexsem pr y, wl) /\
      opv = None /\
      ((ow = $ OS_MUTEX_AVAILABLE /\ y = None )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
      ( (v_ow = (Vint32 ow) /\ O_opt = Some O1) \/
          (v_ow <> (Vint32 ow) /\O_opt = None))
  end.

Definition mutextimedlock_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_tp posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_tp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
        (( v_tp = Vint32 x /\ O_opt = Some O1) \/
          ( v_tp <> Vint32 x /\ O_opt = None ))
  end.

Definition mutextimedlock_typeerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp, 
        vl = ((Vint32 tp) :: rv :: nil) /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false /\
        opv = Some (Vint32(Int.repr EINVAL)) /\
        ((rv = (Vint32(Int.repr EINVAL)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EINVAL)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_normal
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tp, 
        vl = ((Vint32 tp) :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_NORMAL) /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutextimedlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_curp t prio st m sus tls, 
          vl = ( v_curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( v_curp = Vint32 prio /\ O_opt = Some O1) \/
          ( v_curp <> Vint32 prio /\ O_opt = None ))
  end.

Definition mutextimedlock_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pcp posv mls e o x n,
      exists pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_pcp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
        (( v_pcp = Vint32 pcp /\ O_opt = Some O1) \/
          ( v_pcp <> Vint32 pcp /\ O_opt = None ))
  end.

Definition mutextimedlock_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_rcnt posv mls e o x ,
        exists n pro pcp w c mc, 
        vl = ((Vint32 posv) :: v_rcnt :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c, mc) /\
        opv = None /\
          (( v_rcnt = Vint32 n /\ O_opt = Some O1) \/
          ( v_rcnt <> Vint32 n /\ O_opt = None ))
  end.

Definition mutextimedlock_type_deadlk
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_ERRORCHECK) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        opv = Some (Vint32(Int.repr EDEADLK)) /\
        ((rv = (Vint32(Int.repr EDEADLK)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EDEADLK)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_recur_again
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp rcnt, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_recur_incre_one
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv tp ow curp pcp rcnt, 
      exists mls e o x cn pro pip w c mc,
        vl = ((Vint32 posv) :: (Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, cn, pro, pip, w, c, mc) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\
           O_opt = Some (set O1 absmutinfoid 
                                      (absmutinfo (set mls posv (e, o, x, (Int.add cn Int.one), pro, pip, w, c, mc))))) \/
        (rv <> (Vint32 Int.zero) /\ O_opt = None))
  end.

Definition mutextimedlock_after_pend_timeout
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_TIMEOUT) = true /\
        opv = Some(Vint32 (Int.repr ETIMEDOUT)) /\
        (( rv = Vint32 (Int.repr ETIMEDOUT) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr ETIMEDOUT) /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_fail
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_TIMEOUT) = false /\
        Int.eq verr (Int.repr OS_NO_ERR) = false /\
        opv = Some(Vint32 (Int.repr EINVAL)) /\
        (( rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_succ_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: Vnull :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        (( rv = Vint32 Int.zero /\ O_opt = Some O1) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_succ_ecb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr eid posv rv,
      exists mls o x n pro pcp w c mc,
      exists els p ow wl,
        vl = ((Vint32 verr) :: (Vptr eid) :: (Vint32 posv) :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c, mc) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem p ow,wl) /\
        (( rv = Vint32 Int.zero 
            /\ O_opt = Some (set O1 absmutinfoid 
                                            (absmutinfo (set mls posv (Valid_Addr eid, ow, x, n, pro, pcp, w, c, mc))))) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutextimedlock_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (v_pevent, Vnull, Vnull))))
  end.

Definition mutextimedlock (vl: vallist) :=
match vl with
    (V_mux :: V_tm :: V_pos :: V_eid0 :: V_eid :: V_ow :: V_tp :: V_curp :: V_pcp :: V_rcnt ::  V_pevt :: V_err :: V_afteid :: V_ret ::
      vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil)=>
             (mutextimedlock_muxerr (| V_mux :: V_pos :: nil |) ??
               mutextimedlock_mutex_pos (| V_mux :: V_pos :: nil |)) ;;
             (mutextimedlock_poserr (| V_pos :: V_ret :: nil |) ??
               partition_pos_rgn (V_pos :: vr_temp_dom :: vr_temp_num ::
                                                     vr_temp_dom' :: vr_temp_num' :: nil)
               (mutextimedlock_timeout_err (| V_tm :: V_ret :: nil |) ??
               (mutextimedlock_ecb_ptr (| V_pos :: V_eid0 :: nil |) ;;
                    (mutextimedlock_ecb_nullerr (| V_eid0 :: V_ret :: nil |) ??
                        (mutextimedlock_ecb_ptr (| V_pos :: V_eid :: nil |) ;;
                          (mutextimedlock_ecb_nullerr (| V_eid :: V_ret :: nil |) ??
                            mutextimedlock_owner (| V_pos :: V_eid :: V_ow :: nil |) ;;
                            mutextimedlock_type (| V_pos :: V_tp :: nil |) ;;
                                (mutextimedlock_typeerr (| V_tp :: V_ret :: nil |) ??
                                    (mutextimedlock_curprio (| V_curp :: nil |) ;;
                                     mutextimedlock_prioceiling (| V_pos :: V_pcp :: nil |) ;;
                                      (mutextimedlock_type_deadlk (| V_tp :: V_ow :: V_curp :: V_pcp :: V_ret :: nil |) ??
                                        (mutextimedlock_recurcnt (| V_pos :: V_rcnt :: nil |) ;;
                                                (mutextimedlock_type_recur_incre_one (| V_pos :: V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |) ??
                                                  mutextimedlock_type_recur_again (| V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |))) ??
                                        (mutextimedlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                                          mutextimedlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                                          spec_code_cons (mutexpend (V_pevt :: V_tm :: V_err :: nil))
                                          (mutextimedlock_set_evloc_ptr (| Vnull :: nil |) ;;
                                            (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                                            mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                                              (mutextimedlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                                                  (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                                                    mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) ) ??
                              ( mutextimedlock_type_normal (| V_tp :: nil |) ;;
                                    mutextimedlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                                       mutextimedlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                                          spec_code_cons (mutexpend (V_pevt :: V_tm :: V_err :: nil))
                                          (mutextimedlock_set_evloc_ptr (| Vnull :: nil |) ;;
                                            (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                                            mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                                              (mutextimedlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                                                  (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                                                    mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) )))) ) )
  | _ => spec_abort
  end.

Definition mutextimedlockapi:=(mutextimedlock, (Tint32,Tptr pthread_mutex_t:: Tint16 :: nil)).


(* (****************************** pthread_mutex_unlock ************************************) *)

Definition mutexunlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutexunlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = ((Vptr a) :: v' :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition mutexunlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutexunlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pi pro,
        exists c mc,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
          (((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutexunlock_get_ecb_ptr1 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c mc ptrmp t, 
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
         Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Null, o, x, n, pro, pi, w, c, mc) /\
    get O1 evptrid = Some (evptr ptrmp) /\ 
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition mutexunlock_get_ecb_ptr2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c mc ptrmp t eid, 
    vl = ((Vint32 posv) :: v' :: nil) /\
     ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
         Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t ( Vptr eid, Vnull, Vnull)))) \/ 
     v' <> Vptr eid /\ O_opt = None)
  end.

Definition mutexunlock_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists posv mls o x n pro pi w c mc, 
    vl = ((Vint32 posv) :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr (OS_USER_MAX_EVENTS / 3)) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Holder, o, x, n, pro, pi, w, c, mc) /\
    O_opt = None 
  end.

Definition mutexunlock_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((v' = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end. 

Definition mutexunlock_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = (Vptr eid) :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mutexunlock_if_null_owner_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n w pi pro, 
        exists c mc qls pr y wl rv,
      vl =((Vint32 posv) :: (Vptr eid) :: rv :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c, mc) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls eid =Some (absmutexsem pr y, wl) /\
        ((y = None /\ ow = $ OS_MUTEX_AVAILABLE   )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
          ( (rv = (Vint32 ow) /\ O_opt = Some O1) \/
           (rv <> (Vint32 ow) /\O_opt = None) )/\
        opv = None 
  end. 

Definition mutexunlock_recurtype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pi pro,
        exists c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
        opv = None  /\
          (( v' = Vint32 x /\ O_opt = Some O1) \/
          ( v' <> Vint32 x /\ O_opt = None ))
  end.

Definition mutexunlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists curp t prio st m sus tls, 
          vl = ( curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( curp = Vint32 prio /\ O_opt = Some O1) \/
          ( curp <> Vint32 prio /\ O_opt = None ))
  end. 

Definition mutexunlock_prioceil
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv v' mls e o x n w pi pro,
        exists c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
        opv = None /\
        (( v' = Vint32 pi /\ O_opt = Some O1) \/
        ( v' <> Vint32 pi /\ O_opt = None ))
  end.

Definition mutexunlock_get_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x pi ,
        exists n w pro c mc, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c, mc) /\
        opv = None /\
        (( v' = Vint32 n /\ O_opt = Some O1) \/
        ( v' <> Vint32 n /\ O_opt = None ))
  end.

Definition mutexunlock_recvcnt_decrement_oweq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists cn posv x tp ow curp mls eid o w , 
      exists pi pro pe c mc priocl,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl):: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, x, cn, pro, pi, w, c, mc) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
       ( ow = curp \/ priocl = curp ) /\
        opv = None /\
        O_opt = Some (set O1 absmutinfoid (absmutinfo (set mls posv (pe, o, x, (Int.sub cn Int.one), pro, pi, w, c, mc))))
  end.

Definition mutexunlock_if_ow_curp_neq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv ow tp curp eid rv priocl, 
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: rv :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        Vint32 ow <> Vint32 curp /\
        Vint32 priocl <> Vint32 curp /\
        opv = Some (Vint32 (Int.repr EPERM)) /\
        ((rv = (Vint32 (Int.repr EPERM)) /\ O_opt = Some O1) \/
        (rv <> (Vint32 (Int.repr EPERM)) /\ O_opt = None))
  end.

Definition mutexunlock_if_rcnt_zero_neq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv posv  eid rcnt, 
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 rcnt ) :: rv :: nil) /\
        Int.eq rcnt Int.zero =false /\
        opv = Some (Vint32 (Int.zero)) /\
        ((rv = (Vint32 (Int.zero)) /\ O_opt = Some O1) \/
        (rv <> (Vint32 (Int.zero)) /\ O_opt = None)) 
  end.

Definition mutexunlock_set_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists ptrmp t,
        vl = nil /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, Vnull))))
  end.

Definition mutexunlock_afterpost_rv1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
         vl = (Vint32 v) :: nil /\
          Int.eq v (Int.repr OS_ERR_NOT_MUTEX_OWNER) = true /\
          opv = Some (Vint32 (Int.repr EPERM)) /\
         O_opt = Some O1
  end.

Definition mutexunlock_afterpost_rv2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
         vl = (Vint32 v) :: nil /\
         Int.eq v (Int.repr OS_ERR_NOT_MUTEX_OWNER) = false /\
         Int.eq v (Int.repr 0) = false /\
         opv = Some (Vint32 (Int.repr EINVAL)) /\
         O_opt = Some O1
  end.

Definition mutexunlock_afterpost_rv3
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
         vl = (Vint32 v) :: nil /\
          Int.eq v (Int.repr OS_ERR_NOT_MUTEX_OWNER) = false /\
          Int.eq v (Int.repr 0) = true /\
          opv = Some (Vint32 (Int.repr 0)) /\
         O_opt = Some O1
  end.

Definition muxpost (V_pos:val)(V_pevt:val)(V_postrv:val) :=
           (mutexunlock_get_ecb_ptr1 (|V_pos:: V_pevt :: nil|)??
             mutexunlock_get_ecb_ptr2 (|V_pos:: V_pevt :: nil|)??
             mutexunlock_ecb_ptr_holder_abt(|V_pos :: nil|)) ;;
           spec_code_cons (mutexpost (V_pevt :: V_postrv::nil))
                   (mutexunlock_set_ptr (| nil |) ;; 
                    (mutexunlock_afterpost_rv1 (| V_postrv::nil |) ??
                     mutexunlock_afterpost_rv2 (| V_postrv::nil |) ??
                     mutexunlock_afterpost_rv3 (| V_postrv::nil |)) ).

Definition mutexunlock (vl: vallist) :=
match vl with
    (V_mux :: V_pos :: V_eid :: V_ow :: V_tp :: V_curp :: V_priocl :: V_pevt :: V_rcnt :: V_eid0 :: V_ret ::
      vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil)=>
                  (mutexunlock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutexunlock_mutex_pos(|V_mux :: V_pos :: nil|));;
                      (mutexunlock_poserr (|V_pos :: V_ret :: nil|) ?? 
                         (mutexunlock_ecb_ptr (|V_pos :: V_eid :: nil|);; 
                            (mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutexunlock_if_null_no (|V_eid :: nil|) ;;
                                mutexunlock_ecb_ptr (|V_pos :: V_eid0 :: nil|) ;;
                                (mutexunlock_if_null_yes (|V_eid0 :: V_ret :: nil|) ??
                                   (mutexunlock_if_null_owner_no (|V_pos :: V_eid0 :: V_ow :: nil|) ;;
                                     partition_pos_rgn (V_pos :: vr_temp_dom :: vr_temp_num ::
                                                                           vr_temp_dom' :: vr_temp_num' :: nil)
                                        (mutexunlock_recurtype(|V_pos :: V_tp :: nil|) ;; 
                                          ((  mutexunlock_curprio(| V_curp :: nil|) ;; mutexunlock_prioceil(|V_pos :: V_priocl :: nil|) ;;
                                                (  ( mutexunlock_recvcnt_decrement_oweq(|V_pos :: V_eid0 :: V_ow :: V_tp :: V_curp :: V_priocl :: nil|) ;;
                                                       (  mutexunlock_get_recurcnt (|V_pos :: V_rcnt :: nil|) ;; 
                                                           ( mutexunlock_if_rcnt_zero_neq (|V_pos :: V_eid0  :: V_rcnt :: V_ret :: nil|) ??
                                                           ( muxpost V_pos V_pevt V_ret)
                                                            ))) ??
                                                   mutexunlock_if_ow_curp_neq (|V_pos :: V_eid0 :: V_ow :: V_tp :: V_curp :: V_priocl :: V_ret :: nil|))
                                                )??
                                                ( muxpost V_pos V_pevt V_ret)
                                          ))))))))
  | _ => spec_abort
  end.

Definition mutexunlockapi:=(mutexunlock, (Tint32,Tptr pthread_mutex_t::nil)).


(* (****************************** mq_create ************************************) *)

Definition mqcreate_max_msgs_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists max_msgs  rv ,
          vl= (Vint32  max_msgs :: rv :: nil )/\
          Int.ltu max_msgs Int.zero = true /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.
  
Definition mqcreate_msg_size_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists msg_size  rv ,
          vl= (Vint32 msg_size :: rv :: nil )/\
          Int.ltu msg_size Int.zero = true /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition mqcreate_mq_blockflag_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mq_blockflag  rv ,
          vl= (Vint32 mq_blockflag :: rv :: nil )/\
          (Int.eq mq_blockflag Int.zero = false /\
          Int.eq mq_blockflag (Int.repr O_NONBLOCK) = false) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition mqcreate_waitq_type_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists waitq_type  rv ,
          vl= (Vint32 waitq_type :: rv :: nil )/\
          Int.eq waitq_type (Int.repr PTHREAD_WAITQ_PRIO) = false /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.
  
Definition mqcreate_iserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = nil /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition mqcreate_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv qtls idx cpn left right, 
      vl = (posv :: Vint32 idx :: Vint32 cpn :: nil) /\
       get O1 absmqattrid = Some (absmqattr qtls) /\
       left = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx)%Z /\
       right = (OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1))%Z /\
      (
      ((~(exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\ 
                                                 (left <= (Int.unsigned pos) < right)%Z) /\
          posv = Vint32 (Int.repr 255)) \/
       (exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\
         posv = Vint32 pos )) /\ O_opt = Some O1
      ) \/
      (
      ((~(exists pos wtype flag maxm msize curm mqc, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\ 
                                                 (left <= (Int.unsigned pos)  < right)%Z) /\
      posv <> Vint32 (Int.repr 255)) \/
     (exists pos wtype flag maxm msize curm mqc,  get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm, mqc) /\
      posv <> Vint32 pos )) /\ O_opt = None
      )
end.

Definition mqcreate_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos, 
      vl = ((Vint32 pos) :: nil) /\ 
      Int.eq pos (Int.repr 255) = true /\
      opv = Some (Vint32 (Int.mone)) /\
      O_opt = Some O1
  end.

Definition mqcreate_set_placeholder
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos qtls et wtype flag maxm msize curm mqc,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      opv = None /\
      O_opt = Some (set O1 absmqattrid (absmqattr (set qtls pos ( Holder, wtype, flag, maxm, msize, curm, mqc) )))
  end.

Definition mqcreate_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t qtls qtls' ,
    exists et wtype flag maxm msize curm mqc,
    exists locmp locmp' ptrmp ptrmp' muxp semp qp,
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      get O1 curtid = Some (oscurt t) /\
      get O1 evlocid = Some (evloc locmp) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\
      get O1 evptrid = Some (evptr ptrmp) /\
      get ptrmp t = Some (muxp, semp, qp) /\
      ptrmp' = set ptrmp t (muxp, semp, Vnull) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr /\ qtls' = set qtls pos (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc))) 
        \/ eptr = Vnull /\ qtls' = set qtls pos (Null, wtype, flag, maxm, msize, curm, mqc)) /\  
       O_opt = Some (set (set (set O1 absmqattrid (absmqattr qtls')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
  end.

Definition mqcreate_holder_abt
           (vl: vallist) (O: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = Vptr vhold_addr :: nil /\ O_opt = None
  end. 

Definition mqcreate_create_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos, 
    vl = (Vint32 pos :: Vnull :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    opv = Some (Vint32 (Int.mone)) /\
    O_opt = Some O1 
  end.
  
Definition mqcreate_set_maxmsg
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos max_msgs qtls qtls', 
      exists et wtype flag maxm msize curm mqc,
      vl = (Vint32 pos) :: (Vint32 max_msgs) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, flag, max_msgs, msize, curm, mqc) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_msgsize
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos msg_size qtls qtls', 
      exists et wtype flag maxm msize curm mqc,
      vl = (Vint32 pos) :: (Vint32 msg_size) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, flag, maxm, msg_size, curm, mqc) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_flags
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos mq_blockflag qtls qtls', 
      exists et wtype flag maxm msize curm mqc,
      vl = (Vint32 pos) :: (Vint32 mq_blockflag) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, mq_blockflag, maxm, msize, curm, mqc) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_waittype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos  qtls qtls', 
      exists et wtype flag maxm msize curm mqc,
      vl = (Vint32 pos) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm, mqc) /\
      opv = Some (Vint32 pos) /\
      qtls' = set qtls pos ( et, (Int.repr PTHREAD_WAITQ_PRIO), flag, maxm, msize, curm, mqc) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls'))
  end.

Definition mqcreate_rv_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos rv ,
      vl = (Vint32 pos) :: rv :: nil /\
      opv = Some (Vint32 pos) /\
      (rv = (Vint32 pos) /\  O_opt = Some O1 \/
      rv <> Vint32 pos /\ O_opt = None) 
  end.

Definition cast_res v := 
  match v with 
      Vint32 i => Vint32 (Int.modu i (Int.repr Int16.modulus)) 
    | _ => v 
  end.

Definition mqcreate (vl:vallist) :=
  match vl with
    mq_blockflag :: max_msgs :: msg_size :: waitq_type :: posv :: rv_cre ::  rv :: vr_temp_dom :: vr_temp_num :: nil  =>
        mqcreate_max_msgs_err (|max_msgs :: rv :: nil|) ??
        mqcreate_msg_size_err (|msg_size :: rv :: nil|) ??
        mqcreate_mq_blockflag_err (|mq_blockflag :: rv :: nil|) ??
        mqcreate_waitq_type_err (|waitq_type :: rv :: nil|) ??
        mqcreate_iserr (| nil |) ??
        (kscurdom_ext (| nil |) ;;
         get_temp_dom (| vr_temp_dom :: nil |) ;;
         get_temp_num (| vr_temp_num :: nil |) ;;
         mqcreate_pos (| posv :: vr_temp_dom :: vr_temp_num :: nil |) ;;
          (mqcreate_poserr (| posv ::nil |) ??
            (mqcreate_set_placeholder (| posv ::nil |) ;;
             qcre (cast_res max_msgs :: rv_cre :: nil ) ;;   
             (mqcreate_set_ecb_ptr (| posv :: rv_cre :: nil |) ?? mqcreate_holder_abt (| rv_cre :: nil|));;
              (mqcreate_create_err (| posv :: rv_cre :: nil |) ?? 
              mqcreate_set_maxmsg (| posv :: max_msgs :: nil |) ;;
              mqcreate_set_msgsize (| posv :: msg_size :: nil |) ;;
              mqcreate_set_flags (| posv :: mq_blockflag :: nil |) ;;
              mqcreate_set_waittype (| posv :: nil |) ;;
              mqcreate_rv_pos (| posv :: rv :: nil |)
              )
            )
          )
        )
       | _ => spec_abort
  end.

Definition mqcreateapi := (mqcreate, (Tint32, Tint32 :: Tint32 :: Tint32 :: Tint32 ::nil) ).


(* (****************************** mq_delete ************************************) *)

Definition mqdelete_mqdes_err
           (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists mqdes,
      vl= (Vint32 mqdes :: nil )/\
      (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
       mqdes = (Int.repr (OS_USER_MAX_EVENTS / 3))) /\
      opv = Some (Vint32 (Int.mone)) /\
      O_opt = Some O1 
  end.

Definition mqdelete_ecb_ptr_null
      (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes qeibs wtype flag maxm msize curm mqc, 
    vl = ((Vint32 mqdes) :: nil) /\ 
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Null, wtype, flag, maxm, msize, curm, mqc) /\
    opv = Some (Vint32 (Int.mone)) /\
    O_opt = Some O1
  end. 
    
Definition mqdelete_int_nst_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes,
    vl = ((Vint32 mqdes :: nil)) /\
    opv = Some (Vint32 (Int.mone)) /\
    O_opt = Some O1
  end. 

Definition mqdelete_ecb_ptr_holder_abt
      (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes qeibs wtype flag maxm msize curm mqc, 
    vl = ((Vint32 mqdes) :: nil) /\ 
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Holder, wtype, flag, maxm, msize, curm, mqc) /\
    opv = None /\
    O_opt = None 
  end. 

Definition mqdelete_get_set_ecb_ptr
      (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes qeibs wtype flag maxm msize curm mqc t, 
    exists eid v' qeibs' locmp ptrmp locmp' ptrmp',
    vl = ((Vint32 mqdes) :: v' :: nil) /\ 
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Valid_Addr eid, wtype, flag, maxm, msize, curm, mqc) /\ 
    get O1 curtid = Some (oscurt t) /\
    get O1 evlocid = Some (evloc locmp) /\
    get locmp t = Some (Vint32 ($ __EvLoc_normal)) /\ 
    get O1 evptrid = Some (evptr ptrmp) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\
    qeibs' = set qeibs mqdes (Null, wtype, flag, maxm, msize, curm, mqc) /\ 
    locmp' = set locmp t (Vint32 ($ __EvLoc_ecbdel)) /\  
    ptrmp' = set ptrmp t (Vnull, Vnull, Vptr eid) /\
    opv = None /\
    (v' = Vptr eid /\
     O_opt = Some (set (set (set O1 absmqattrid (absmqattr qeibs'))
                            evlocid (evloc locmp')) evptrid (evptr ptrmp')) \/  
     v' <> Vptr eid /\ O_opt = None) 
  end.

Definition mqdelete_reset_loc
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes t locmp ptrmp locmp', 
    vl = ((Vint32 mqdes) :: nil) /\ 
    get O1 curtid = Some (oscurt t) /\
    get O1 evlocid = Some (evloc locmp) /\
    get locmp t = Some (Vint32 ($ __EvLoc_ecbdel)) /\ 
    get O1 evptrid = Some (evptr ptrmp) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\
    locmp' = set locmp t (Vint32 ($ __EvLoc_normal)) /\  
    opv = Some (Vint32 Int.zero) /\
    O_opt = Some (set O1 evlocid (evloc locmp'))
  end.

Definition mqdelete (vl: vallist) :=
  match vl with 
    v1 :: v2 :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil =>
    mqdelete_mqdes_err (| v1 :: nil |) ??
    partition_pos_rgn (v1 :: vr_temp_dom :: vr_temp_num ::
                                          vr_temp_dom' :: vr_temp_num' :: nil)
    (mqdelete_ecb_ptr_null (| v1 :: nil |) ??
    mqdelete_ecb_ptr_holder_abt (| v1 :: nil |) ?? 
    mqdelete_int_nst_err (| v1 :: nil |) ??
    (mqdelete_get_set_ecb_ptr (| v1 :: v2 :: nil |) ;;
     spec_code_cons
       (qdel (v2::nil))
       (mqdelete_reset_loc (| v1 :: nil |))))
  | _ => ABORT
  end.

Definition mqdeleteapi := (mqdelete, (Tint32, mqd_t :: nil)).  


(* (****************************** memcpy (stub) ***********************************) *) 

Definition memcpy_empty (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists   v1 v2 v3 p,
       vl =  (v1 :: v2 :: v3 :: nil) /\
       opv = Some (Vptr p)
  end.

Definition memcpy_spec (vl:vallist) :=
  match vl with
      v1 :: v2 :: v3 :: nil =>
          memcpy_empty(|v1::v2::v3::nil |)
      | _ => spec_abort
  end.


(* (******************************  mq_receive ***********************************) *)

Definition qreceive_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
          mqdes = (Int.repr (OS_USER_MAX_EVENTS / 3))) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition qreceive_get_msgsize  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr (OS_USER_MAX_EVENTS / 3)) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 msize) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 msize) /\ O_opt =  None)
             )
  end.

Definition qreceive_if_msgsizelt_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize v' len,
      (vl =  len ::  (Vint32 msize) :: v' :: nil) /\
      Int.ltu msize msg_len = true /\
      len = Vint32 msg_len /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition qreceive_if_msgsizelt_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize,
      (vl =  (Vint32 msg_len) ::  (Vint32 msize) :: nil) /\
      (Int.ltu msize msg_len   = false )/\
        opv = None /\
        O_opt = Some O1
  end. 

Definition qreceive_msgptr_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists msg_ptr  rv ,
        vl=  msg_ptr  :: rv :: nil /\
        (msg_ptr = Vnull \/
           exists a,
             msg_ptr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some  (Vint32 (Int.mone)) /\  
        (rv = (Vint32 (Int.mone))  /\ O_opt = Some O1   \/ 
         rv <>  (Vint32 (Int.mone))  /\ O_opt = None   )
  end.
  
Definition qreceive_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm mqc,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
           (
               ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
                    /\ O_opt = Some O1
           \/
             (  ((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull)     )
                /\ O_opt = None
          )
end.

Definition qreceive_if_null_yes    
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition qreceive_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition qreceive_get_mqflags  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
(*           ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\ *)
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 flag) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 flag) /\ O_opt =  None)
             )
  end.

Definition qreceive_mqflags_noteq_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag  v',
      (vl = (Vint32 flag)  :: v' :: nil) /\
      ( Int.eq flag Int.zero = false /\ Int.eq flag (Int.repr O_NONBLOCK) = false ) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ( (v' = Vint32 (Int.mone) /\ O_opt = Some O1)
           \/
          (v' <> Vint32(Int.mone) /\ O_opt = None)   )
  end. 

Definition qreceive_mqflags_noteq_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  flag ,
      (vl =  (Vint32 flag) :: nil) /\
      (Int.eq flag Int.zero  = true \/ Int.eq flag (Int.repr O_NONBLOCK)  = true )/\
        opv = None /\
        O_opt = Some O1
  end. 

Definition qreceive_perr_not_null 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists perr perr',
      (vl =  perr :: nil) /\
             (  (perr = (Vptr perr') /\ O_opt = Some O1)
              \/
                ( perr = Vnull /\ O_opt =  None)
             )
  end.

Definition qreceive_mqflags_noteqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = false /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition qreceive_mqflags_eqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = true /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition qreceive_msg_null_flageq1_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.one = true /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end. 

Definition qreceive_msg_null_flageq0_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.zero = true /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end.
  
Definition qreceive_msg_null_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.zero = false /\
      Int.eq flag Int.one = false /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end.
  
Definition qreceive_succ_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret msg_len,
      (vl = Vint32 msg_len :: msg  :: ret  :: nil) /\
      msg  <> Vnull /\ 
      opv = Some (Vint32 (msg_len)) /\ 
        ((ret = Vint32 (msg_len) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(msg_len) /\ O_opt = None) )
  end.
  
Definition mqreceive_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.
    
Definition qreceive_ret (mqdes: val)(rv_flag'':val)(rv_post: val)(msg_len:val) ( rv : val) (msg_ptr:val) :=
      mqreceive_set_evloc_ptr (|Vnull :: nil|) ;;
      qreceive_get_mqflags (| mqdes :: rv_flag'' :: nil|) ;; 
      (qreceive_msg_null_flageq1_ret  (|rv_flag''::rv_post :: rv :: nil|)  ??
        qreceive_msg_null_flageq0_ret (|rv_flag'':: rv_post :: rv :: nil|)  ??
        qreceive_msg_null_ret  (|rv_flag'':: rv_post :: rv :: nil|) ??
        spec_code_cons (memcpy_spec (msg_ptr :: rv_post :: msg_len :: nil)) (qreceive_succ_ret(|msg_len::rv_post::rv::nil|))).
  
Definition mqreceive (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: perr :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post':: rv_post  :: rv :: rv_flag'' ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil  =>
        qreceive_mqdes_err (| mqdes :: rv :: nil|) ??
        partition_pos_rgn (mqdes :: vr_temp_dom :: vr_temp_num ::
                                              vr_temp_dom' :: vr_temp_num' :: nil)
(*         qreceive_timeout_err(|abs_timeout :: rv :: nil|)?? *)
        (qreceive_get_msgsize (|mqdes :: rv_size :: nil|) ;;
            ( qreceive_if_msgsizelt_yes (|msg_len :: rv_size :: rv :: nil|) ?? 
              qreceive_if_msgsizelt_no (|msg_len :: rv_size :: nil|) ;;
                 ( qreceive_msgptr_err (| msg_ptr :: rv :: nil|) ??
                  qreceive_get_ecb_ptr (|mqdes :: rv_ptr :: nil|) ;;
                    ( qreceive_if_null_yes (| rv_ptr :: rv :: nil|) ??
                      qreceive_if_null_no (| rv_ptr :: nil|) ;;
                        ( qreceive_get_mqflags (| mqdes :: rv_flag :: nil|) ;;
                            ( qreceive_mqflags_noteq_yes (| rv_flag :: rv :: nil|) ??
                              qreceive_mqflags_noteq_no (| rv_flag  :: nil|) ;;
                                ( qreceive_get_mqflags (| mqdes :: rv_flag' :: nil|) ;; 
                                   (( qreceive_mqflags_eqzero_beforepost (| rv_flag' :: nil|) ;;
                                      qreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;mqreceive_set_evloc_ptr(|rv_ptr' :: nil|) ;; qreceive_perr_not_null(|perr :: nil|);;
                                      (spec_code_cons
                                       (qpendnew (rv_ptr' :: Vint32 (Int.repr 0) :: perr :: rv_post :: nil)) 
                                       (qreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                        ??
                                    ( qreceive_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       qreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                       mqreceive_set_evloc_ptr (|rv_ptr' :: nil|) ;;
                                       (spec_code_cons
                                        (qacceptnew (rv_ptr' :: rv_post :: nil))
                                        (qreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                      ))))))))
       | _ => spec_abort
  end.
  
Definition mqreceiveapi := (mqreceive, (ssize_t, mqd_t :: Tptr char :: size_t :: unsigned :: Tptr Int8u ::nil) ). 


(* (******************************  mq_timedreceive ***********************************) *)

Definition qtimedreceive_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr  (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
          mqdes =(Int.repr  (OS_USER_MAX_EVENTS / 3))) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition qtimedreceive_timeout_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists timeout  rv ,
          vl= (Vint32 timeout :: rv :: nil )/\
          ( Int.ltu (Int.repr 65535) timeout = true \/ timeout =(Int.repr 0)) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.
  
Definition qtimedreceive_get_msgsize  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr (OS_USER_MAX_EVENTS / 3)) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 msize) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 msize) /\ O_opt =  None)
             )
  end.

Definition qtimedreceive_if_msgsizelt_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize v' len,
      (vl =  len ::  (Vint32 msize) :: v' :: nil) /\
      Int.ltu msize msg_len = true /\
      len = Vint32 msg_len /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

  
Definition qtimedreceive_if_msgsizelt_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize,
      (vl =  (Vint32 msg_len) ::  (Vint32 msize) :: nil) /\
      (Int.ltu msize msg_len   = false )/\
        opv = None /\
        O_opt = Some O1
  end. 

Definition qtimedreceive_msgptr_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists msg_ptr  rv ,
        vl=  msg_ptr  :: rv :: nil /\
        (msg_ptr = Vnull \/
           exists a,
             msg_ptr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some  (Vint32 (Int.mone)) /\  
        (rv = (Vint32 (Int.mone))  /\ O_opt = Some O1   \/ 
         rv <>  (Vint32 (Int.mone))  /\ O_opt = None   )
  end.
  
Definition qtimedreceive_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm mqc,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
           (
               ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
                    /\ O_opt = Some O1
           \/
             (  ((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull)     )
                /\ O_opt = None
          )
end.

Definition qtimedreceive_if_null_yes    
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition qtimedreceive_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition qtimedreceive_get_mqflags  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
(*           ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\ *)
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 flag) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 flag) /\ O_opt =  None)
             )
  end.

Definition qtimedreceive_mqflags_noteq_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag  v',
      (vl = (Vint32 flag)  :: v' :: nil) /\
      ( Int.eq flag Int.zero = false /\ Int.eq flag (Int.repr O_NONBLOCK) = false ) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ( (v' = Vint32 (Int.mone) /\ O_opt = Some O1)
           \/
          (v' <> Vint32(Int.mone) /\ O_opt = None)   )
  end. 

Definition qtimedreceive_mqflags_noteq_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  flag ,
      (vl =  (Vint32 flag) :: nil) /\
      (Int.eq flag Int.zero  = true \/ Int.eq flag (Int.repr O_NONBLOCK)  = true )/\
        opv = None /\
        O_opt = Some O1
  end. 


Definition qtimedreceive_perr_not_null 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists perr perr',
      (vl =  perr :: nil) /\
             (  (perr = (Vptr perr') /\ O_opt = Some O1)
              \/
                ( perr = Vnull /\ O_opt =  None)
             )
  end.


Definition qtimedreceive_mqflags_noteqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = false /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition qtimedreceive_mqflags_eqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = true /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition qtimedreceive_msg_null_flageq1_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.one = true /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end. 

Definition qtimedreceive_msg_null_flageq0_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.zero = true /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end.
  
Definition qtimedreceive_msg_null_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret flag,
      (vl = (Vint32 flag) :: msg  :: ret  :: nil) /\
      msg  = Vnull /\ 
      Int.eq flag Int.zero = false /\
      Int.eq flag Int.one = false /\
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end.
  
Definition qtimedreceive_succ_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg ret msg_len,
      (vl = Vint32 msg_len :: msg  :: ret  :: nil) /\
      msg  <> Vnull /\ 
      opv = Some (Vint32 (msg_len)) /\ 
        ((ret = Vint32 (msg_len) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(msg_len) /\ O_opt = None) )
  end.

Definition qtimedreceive_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.

Definition qtimedreceive_ret (mqdes: val)(rv_flag'':val)(rv_post: val)(msg_len:val) ( rv : val) (msg_ptr : val):=
      qtimedreceive_set_evloc_ptr (|Vnull :: nil|) ;;
      qtimedreceive_get_mqflags (| mqdes :: rv_flag'' :: nil|) ;; 
     (qtimedreceive_msg_null_flageq1_ret  (|rv_flag''::rv_post :: rv :: nil|)  ??
      qtimedreceive_msg_null_flageq0_ret (|rv_flag'':: rv_post :: rv :: nil|)  ??
      qtimedreceive_msg_null_ret  (|rv_flag'':: rv_post :: rv :: nil|) ??
      spec_code_cons(memcpy_spec (msg_ptr :: rv_post :: msg_len :: nil)) (qtimedreceive_succ_ret(|msg_len::rv_post::rv::nil|))).
  
Definition mqtimedreceive (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: abs_timeout :: perr :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post':: rv_post  :: rv :: rv_flag'' ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil  =>
        qtimedreceive_mqdes_err (| mqdes :: rv :: nil|) ??
        partition_pos_rgn (mqdes :: vr_temp_dom :: vr_temp_num ::
                                              vr_temp_dom' :: vr_temp_num' :: nil)
        (qtimedreceive_timeout_err(|abs_timeout :: rv :: nil|)??
        qtimedreceive_get_msgsize (|mqdes :: rv_size :: nil|) ;;
            ( qtimedreceive_if_msgsizelt_yes (|msg_len :: rv_size :: rv :: nil|) ?? 
              qtimedreceive_if_msgsizelt_no (|msg_len :: rv_size :: nil|) ;;
                 ( qtimedreceive_msgptr_err (| msg_ptr :: rv :: nil|) ??
                  qtimedreceive_get_ecb_ptr (|mqdes :: rv_ptr :: nil|) ;;
                    ( qtimedreceive_if_null_yes (| rv_ptr :: rv :: nil|) ??
                      qtimedreceive_if_null_no (| rv_ptr :: nil|) ;;
                        ( qtimedreceive_get_mqflags (| mqdes :: rv_flag :: nil|) ;;
                            ( qtimedreceive_mqflags_noteq_yes (| rv_flag :: rv :: nil|) ??
                              qtimedreceive_mqflags_noteq_no (| rv_flag  :: nil|) ;;
                                ( qtimedreceive_get_mqflags (| mqdes :: rv_flag' :: nil|) ;; 
                                   (( qtimedreceive_mqflags_eqzero_beforepost (| rv_flag' :: nil|) ;;
                                      qtimedreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;qtimedreceive_set_evloc_ptr(|rv_ptr' :: nil|) ;; qtimedreceive_perr_not_null(|perr :: nil|);;
                                      (spec_code_cons
                                       (qpendnew (rv_ptr' :: abs_timeout :: perr :: rv_post :: nil)) 
                                       (qtimedreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                        ??
                                    ( qtimedreceive_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       qtimedreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;; qtimedreceive_set_evloc_ptr(|rv_ptr' :: nil|) ;;
                                       (spec_code_cons
                                        (qacceptnew (rv_ptr' :: rv_post :: nil))
                                        (qtimedreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                      ))))))))
       | _ => spec_abort
  end.
  
Definition mqtimedreceiveapi := (mqtimedreceive, (ssize_t, mqd_t :: Tptr char :: size_t ::Tptr unsigned :: Int16u :: Tptr Int8u ::nil) ). 


(* (******************************  mq_send ***********************************) *)

Definition mqsend_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
          mqdes =(Int.repr (OS_USER_MAX_EVENTS / 3))) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition mqsend_get_msgsize  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr (OS_USER_MAX_EVENTS / 3)) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 msize) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 msize) /\ O_opt =  None)
             )
  end.

Definition mqsend_if_msgsizelt_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize v' len,
      (vl =  len ::  (Vint32 msize) :: v' :: nil) /\
      Int.ltu msize msg_len = true /\
      len = Vint32 msg_len /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition mqsend_if_msgsizelt_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists msg_len msize,
      (vl =  (Vint32 msg_len) ::  (Vint32 msize) :: nil) /\
      (Int.ltu msize msg_len   = false )/\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mqsend_msgptr_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists msg_ptr  rv ,
        vl=  msg_ptr  :: rv :: nil /\
        (msg_ptr = Vnull \/
           exists a,
             msg_ptr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some  (Vint32 (Int.mone)) /\  
        (rv = (Vint32 (Int.mone))  /\ O_opt = Some O1   \/ 
         rv <>  (Vint32 (Int.mone))  /\ O_opt = None   )
  end.

Definition mqsend_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm mqc,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
           (
               ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
                    /\ O_opt = Some O1
           \/
             (  ((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull)     )
                /\ O_opt = None
          )
end.

Definition mqsend_if_null_yes    
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ((v' = Vint32 (Int.mone) /\ O_opt = Some O1)
         \/ (v' <> Vint32(Int.mone) /\ O_opt = None))
  end. 

Definition mqsend_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mqsend_get_mqflags  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm mqc,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
             (  (rv = (Vint32 flag) /\ O_opt = Some O1)
              \/
                ( rv <> (Vint32 flag) /\ O_opt =  None)
             )
  end.

Definition mqsend_mqflags_noteq_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag  v',
      (vl = (Vint32 flag)  :: v' :: nil) /\
      ( Int.eq flag Int.zero = false /\ Int.eq flag (Int.repr O_NONBLOCK) = false ) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        ( (v' = Vint32 (Int.mone) /\ O_opt = Some O1)
           \/
          (v' <> Vint32(Int.mone) /\ O_opt = None)   )
  end. 

Definition mqsend_mqflags_noteq_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  flag ,
      (vl =  (Vint32 flag) :: nil) /\
      (Int.eq flag Int.zero  = true \/ Int.eq flag (Int.repr O_NONBLOCK)  = true )/\
        opv = None /\
        O_opt = Some O1
  end. 


Definition mqsend_mqflags_noteqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = false /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition mqsend_mqflags_eqzero_beforepost
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists flag ,
      (vl = (Vint32 flag) :: nil) /\
      Int.eq flag Int.zero = true /\
      opv = None /\
      O_opt = Some O1
  end. 

Definition mqsend_ret_eqfull
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  post_rv ret ,
      (vl = (Vint32 post_rv)  :: ret  :: nil) /\
      Int.eq post_rv  (Int.repr OS_Q_FULL)= true /\ 
      opv = Some (Vint32 (Int.mone)) /\ 
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1 )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end. 

Definition mqsend_ret_eqnoerr_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  post_rv ret ,
      (vl = (Vint32 post_rv)  :: ret  :: nil) /\
      Int.eq post_rv  (Int.repr OS_NO_ERR)= true /\ 
      Int.eq post_rv  (Int.repr OS_Q_FULL)= false /\ 
      opv = Some (Vint32 (Int.zero)) /\
      ( (ret = Vint32 (Int.zero) /\ O_opt = Some O1  )
         \/ (ret <> Vint32(Int.zero) /\ O_opt = None) )
  end. 

Definition mqsend_ret_eqnoerr_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  post_rv ret ,
      (vl = (Vint32 post_rv)  :: ret  :: nil) /\
      Int.eq post_rv  (Int.repr OS_NO_ERR)= false /\
      Int.eq post_rv  (Int.repr OS_Q_FULL)= false /\ 
      opv = Some (Vint32 (Int.mone)) /\
        ((ret = Vint32 (Int.mone) /\ O_opt = Some O1  )
         \/ (ret <> Vint32(Int.mone) /\ O_opt = None) )
  end. 

Definition mqsend_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.

Definition mqsend_ret (rv_post: val) ( rv : val) :=
      mqsend_ret_eqfull  (|rv_post :: rv :: nil|)  ??
      mqsend_ret_eqnoerr_yes (|rv_post :: rv :: nil|)  ??
      mqsend_ret_eqnoerr_no  (|rv_post :: rv :: nil|) .
 
Definition mqsend (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post  :: rv ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil  =>
        mqsend_mqdes_err (|mqdes :: rv :: nil|) ??
        partition_pos_rgn (mqdes :: vr_temp_dom :: vr_temp_num ::
                                              vr_temp_dom' :: vr_temp_num' :: nil)
        (mqsend_get_msgsize (|mqdes :: rv_size :: nil|) ;;
            ( mqsend_if_msgsizelt_yes (|msg_len :: rv_size :: rv :: nil|) ?? 
              mqsend_if_msgsizelt_no (|msg_len :: rv_size :: nil|) ;;
                 ( mqsend_msgptr_err (| msg_ptr :: rv :: nil|) ??
                  mqsend_get_ecb_ptr (|mqdes :: rv_ptr :: nil|) ;;
                    ( mqsend_if_null_yes (| rv_ptr :: rv :: nil|) ??
                      mqsend_if_null_no (| rv_ptr :: nil|) ;;
                        ( mqsend_get_mqflags (| mqdes :: rv_flag :: nil|) ;;
                            ( mqsend_mqflags_noteq_yes (| rv_flag :: rv :: nil|) ??
                              mqsend_mqflags_noteq_no (| rv_flag  :: nil|) ;;
                                ( mqsend_get_mqflags (| mqdes :: rv_flag' :: nil|) ;;
                                   ( ( mqsend_mqflags_eqzero_beforepost (| rv_flag' :: nil|) ;;
                                      mqsend_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                      mqsend_set_evloc_ptr (| rv_ptr' :: nil |) ;;
                                      (spec_code_cons
                                       (qtimedpost (rv_ptr' :: Vint32 (Int.zero) :: msg_ptr :: rv_post :: nil)) 
                                        (mqsend_set_evloc_ptr (| Vnull :: nil |) ;;
                                        (mqsend_ret rv_post rv  ) ) ))
                                        ??
                                    ( mqsend_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       mqsend_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                       mqsend_set_evloc_ptr (| rv_ptr' :: nil |) ;;
                                       (spec_code_cons
                                        (qpost (rv_ptr' :: msg_ptr :: rv_post :: nil))
                                        (mqsend_set_evloc_ptr (| Vnull :: nil |) ;;
                                        (mqsend_ret rv_post rv ) ) ))
                                      ) )))))))
       | _ => spec_abort
  end.

Definition mqsendapi := (mqsend, (Tint32, mqd_t :: Tptr char :: size_t :: unsigned ::nil) ).


(* (******************************  mq_getinfo ***********************************) *)

Definition mqgetinfo_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  ,
          vl= (Vint32 mqdes :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ mqdes =(Int.repr (OS_USER_MAX_EVENTS / 3))) /\
           opv = Some (Vint32 (Int.mone)) 
  end.

Definition mqgetinfo_mq_info_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mq_info ,
        vl =  mq_info :: nil /\
        (mq_info = Vnull \/
           exists a,
             mq_info = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some  (Vint32 (Int.mone)) 
  end.
  
Definition mqgetinfo_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm mqc,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm, mqc) /\
           (
               ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
                    /\ O_opt = Some O1
           \/
             (  ((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull)     )
                /\ O_opt = None
          )
end.

Definition mqgetinfo_if_null_yes    
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      (vl = Vnull :: nil) /\
        opv = Some (Vint32 (Int.mone)) 
  end. 

Definition mqgetinfo_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = Vptr eid :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 
  
Definition mqgetinfo_query_err_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists query_rv,
      (vl =  Vint32 query_rv :: nil) /\
      Int.eq query_rv Int.zero = false /\
      opv = Some (Vint32 (Int.mone)) 
  end.
  
Definition mqgetinfo_pdata_not_null 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pdata pdata',
      (vl =  pdata :: nil) /\
             (  (pdata = (Vptr pdata') /\ O_opt = Some O1)
              \/
                ( pdata = Vnull /\ O_opt =  None)
             )
  end.
  
Definition mqgetinfo_mq_info_validptr_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mq_info evheap t vl l,
   vl = ((Vptr mq_info) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap mq_info = None \/
        (Get_struct evheap mq_info = Some (mq_info, t, l) /\ t <> mq_info_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mqgetinfo_pdata_validptr_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pdata evheap t vl l,
   vl = ((Vptr pdata) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap pdata = None \/
        (Get_struct evheap pdata = Some (pdata, t, l) /\ t <> OS_Q_DATA) ) /\
   opv = None /\
   O_opt = None
end.

Definition mqgetinfo_query_get_mq_curmsgs
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  mqdes evheap evheap' mq_info pdata vl l l'  ,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) :: (Vptr pdata)  ::  nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l') /\
      evheap' = Set_struct' evheap mq_info mq_curmsgs (nth_val' 1 l')/\
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.

Definition mqgetinfo_query_get_mq_maxmsg
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  mqdes evheap evheap' mq_info pdata vl l l'  ,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) :: (Vptr pdata)  :: nil) /\
  (*     Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l') /\
      evheap' = Set_struct' evheap mq_info mq_maxmsg (nth_val' 2 l')/\
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.

Definition mqgetinfo_query_get_mq_msgsize
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) mqdes evheap evheap' mq_info vl l  ,
      exists qtls e wtype flag maxm msize curm mqc,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) :: nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm, mqc) /\ 
      evheap' = Set_struct' evheap mq_info mq_msgsize (Vint32 msize) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None 
  end.

Definition mqgetinfo_query_get_mq_waittype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) mqdes evheap evheap' mq_info vl l  ,
      exists qtls e wtype flag maxm msize curm mqc,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) ::  nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm, mqc) /\ 
      evheap' = Set_struct' evheap mq_info mq_waittype (Vint32 wtype) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.

Definition mqgetinfo_query_get_mq_flags
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) mqdes evheap evheap' mq_info vl l  ,
      exists qtls e wtype flag maxm msize curm mqc,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) :: nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm, mqc) /\ 
      evheap' = Set_struct' evheap mq_info mq_flags (Vint32 flag) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.
  
Definition mqgetinfo_query_get_task_blocked
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) evheap evheap' mq_info vl l ,
      (vl = (Vptr mq_info) ::(*  Vint32 query_rv :: *) nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      evheap' = Set_struct' evheap mq_info os_code_defs.task_blocked  (Vint32 Int.zero) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.

Definition mqgetinfo_query_after_while_set_blocked
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists sid evheap evheap' mq_info vl l tcbls vblocked vh,
      (vl = (Vptr sid) :: (Vptr mq_info)  :: nil) /\
      get O1 abstcblsid = Some (abstcblist tcbls) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      vblocked = (get_tls_blocked_q_num (TcbMod.lst tcbls) sid) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      Vint32 vh = (nth_val' 5 l) /\
      evheap' = Set_struct' evheap mq_info os_code_defs.task_blocked (Vint32 (Int_add_n vblocked vh Int.one)) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = Some (Vint32 (Int.zero)) 
  end.
  
Definition mqgetinfo_query_memcpy_get_mq_info_oseventtbl
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists  mq_info oseventtbl oseventtbl_addr,
    (vl =  (Vptr mq_info) :: (  oseventtbl )  :: nil) /\
    (((oseventtbl = Vptr oseventtbl_addr /\
        Some oseventtbl_addr =  id_addrval mq_info OSEventTbl mq_info_t ) /\
       O_opt = Some O1)
      \/
      (~(oseventtbl = Vptr oseventtbl_addr /\ Some oseventtbl_addr =  id_addrval mq_info OSEventTbl mq_info_t)  /\
        O_opt =  None)
    )/\ opv = None
  end.
  
Definition mqgetinfo_query_memcpy_get_pdata_oseventtbl
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  pdata oseventtbl oseventtbl_addr,
      (vl =  (Vptr pdata) :: (  oseventtbl )  :: nil) /\
      (  ((oseventtbl = Vptr oseventtbl_addr /\ Some oseventtbl_addr =  id_addrval pdata OSEventTbl OS_Q_DATA) /\ O_opt = Some O1)
         \/
         ( ~(oseventtbl = Vptr oseventtbl_addr /\ Some oseventtbl_addr =  id_addrval pdata OSEventTbl OS_Q_DATA)  /\ O_opt =  None)
      ) /\
      opv = None
  end.
  
Definition mqgetinfo_succ_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      (vl = nil) /\
      O_opt = Some O1  /\
      opv = Some (Vint32 (Int.zero)) 
  end.

Definition mqgetinfo (vl:vallist) :=
  match vl with
    mqdes :: mq_info :: pdata :: rv_ptr :: rv_ptr' :: rv_ptr'' :: rv_ptr''' :: rv_ptr'''':: rv_ptr''''' :: query_rv ::
    rv_for_ptr :: rv_tid_ptr1 :: rv_tid_ptr2 :: rv_tcbevent_ptr :: oseventtbl_addr1::oseventtbl_addr2 ::
    vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil  =>
            mqgetinfo_mqdes_err (|mqdes :: nil|)??
            partition_pos_rgn (mqdes :: vr_temp_dom :: vr_temp_num ::
                                                  vr_temp_dom' :: vr_temp_num' :: nil)
            (mqgetinfo_mq_info_err (| mq_info :: nil|) ??
            mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr :: nil|) ;;
            (
                mqgetinfo_if_null_yes (| rv_ptr :: nil|) ??
                mqgetinfo_if_null_no (| rv_ptr :: nil|) ;;
                mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;; 
                mqgetinfo_pdata_not_null(|pdata :: nil|);;
                (
                  spec_code_cons (qquerynew (rv_ptr' :: pdata :: query_rv :: nil)) 
                   (  mqgetinfo_query_err_ret(|query_rv :: nil |)??
                      (
                         mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                         mqgetinfo_pdata_validptr_err(|pdata :: nil|)??
                         mqgetinfo_query_get_mq_curmsgs(|mqdes :: mq_info :: pdata :: nil|);;
                         (  mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                             mqgetinfo_pdata_validptr_err(|pdata :: nil|)??
                             mqgetinfo_query_get_mq_maxmsg(|mqdes :: mq_info :: pdata :: nil|);;
                             ( mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr'' :: nil|) ;; 
                                mqgetinfo_query_get_mq_msgsize(|mqdes :: mq_info :: nil|);;
                                  (mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                    mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr''' :: nil|) ;; 
                                    mqgetinfo_query_get_mq_waittype(|mqdes :: mq_info :: nil|);;
                                      (mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                        mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr'''' :: nil|) ;; 
                                        mqgetinfo_query_get_mq_flags(|mqdes :: mq_info :: nil|);;
                                          (mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                           mqgetinfo_query_get_task_blocked(| mq_info ::nil|);; mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr''''' :: nil|) ;;(mqgetinfo_if_null_yes (| rv_ptr''''' :: nil|) ??
                mqgetinfo_if_null_no (| rv_ptr''''' :: nil|) ;;(
                  mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                  (mqgetinfo_query_after_while_set_blocked(|rv_ptr''''' :: mq_info ::nil|) ;;      
                            ( mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                             mqgetinfo_pdata_validptr_err(|pdata :: nil|)??
                             mqgetinfo_query_memcpy_get_mq_info_oseventtbl(|mq_info ::oseventtbl_addr1::nil |);;
                              mqgetinfo_query_memcpy_get_pdata_oseventtbl(|pdata ::oseventtbl_addr2::nil |);;
                              spec_code_cons(memcpy_spec (oseventtbl_addr1 :: oseventtbl_addr2 :: V$ OS_EVENT_TBL_SIZE :: nil)) (mqgetinfo_succ_ret(|nil|))))   )
                                              ) 
                                           )
                                      )     
                                 )
                            )
                         )
                      )
                  )
                )
            ))
       | _ => spec_abort
  end.
  
Definition mqgetinfoapi := (mqgetinfo, (Tint32, mqd_t :: Tptr mq_info_t :: Tptr OS_Q_DATA ::nil) ). 

(* end abs ops for GJB functions for events *) 

(* (*************************** end abs op for events *****************************) *)


(*interrupts*)

(* Inductive tickchange : tid -> taskstatus -> EcbMod.map -> taskstatus -> EcbMod.map -> Prop:=
| rdy_change: forall t st els eid, (st=rdy) \/ ( st = wait (os_stat_sem eid) Int.zero)\/ ( st =wait (os_stat_q eid) Int.zero)
                                                        \/ ( st =wait (os_stat_mbox eid) Int.zero) \/ ( st =wait (os_stat_mutexsem eid) Int.zero)
                                                        \/ ( st =wait (os_stat_postq eid) Int.zero)  ->
                                tickchange t st els st els
| wait_change: forall t st els st' n, st =wait os_stat_time n -> (Int.eq Int.one n = false) -> st' =wait os_stat_time (Int.sub n Int.one) ->
                                        tickchange t st els st' els
| wait_rdy_change: forall t st els st', st = wait os_stat_time Int.one -> st' = rdy->
                                          tickchange t st els st' els
| waite_change: forall t st els st' eid n x, 
                  st=wait x n ->
                  (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
                   x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid))->
                  (Int.eq Int.one n = false /\ Int.eq Int.zero n = false ) ->
                  st' = wait x (Int.sub n Int.one) ->
                  tickchange t st els st' els
| waite_rdy_change: forall t st els els' st' eid m wl x,
                      (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
                       x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid)) ->
                      st =wait x Int.one -> st' = rdy ->
                      get els eid = Some (m,wl) ->
                      els' = set els eid (m,remove_tid t wl)->
                      tickchange t st els st' els'. *)

Inductive tickchange : tid -> taskstatus -> EcbMod.map -> taskstatus -> EcbMod.map -> Prop:=
| rdy_change: 
    forall t st els eid,
       (st=rdy) \/
       ( st = wait (os_stat_sem eid) None)\/ ( st =wait (os_stat_q eid) None) \/
       ( st =wait (os_stat_mbox eid) None) \/ ( st =wait (os_stat_mutexsem eid) None) \/
       (st =  wait (os_stat_postq eid) None) \/
       ( st = wait (os_stat_sem eid) (Some Int.zero))\/ ( st =wait (os_stat_q eid) (Some Int.zero)) \/
       ( st =wait (os_stat_mbox eid) (Some Int.zero)) \/ ( st =wait (os_stat_mutexsem eid) (Some Int.zero)) ->
       tickchange t st els st els
| wait_change:
    forall t st els st' n,
      st =wait os_stat_time (Some n) ->
      (Int.eq Int.one n = false) ->
      st' =wait os_stat_time (Some (Int.sub n Int.one)) ->
      tickchange t st els st' els
| wait_rdy_change:
    forall t st els st',
      st = wait os_stat_time (Some Int.one) ->
      st' = rdy-> 
      tickchange t st els st' els
| waite_change:
    forall t st els st' eid n x,
      st=wait x (Some n) ->
      (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
       x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid) 
       \/ x = (os_stat_postq eid))->
      (Int.eq Int.one n = false /\ Int.eq Int.zero n = false ) ->
      st' = wait x (Some (Int.sub n Int.one)) ->
      tickchange t st els st' els
| waite_rdy_change:
  forall t st els st' eid m wl x,
    (x = (os_stat_q eid) \/ x=(os_stat_sem eid) \/
       x=(os_stat_mbox eid) \/ x=(os_stat_mutexsem eid)) ->
    st =wait x (Some Int.one) -> st' = wait x (Some Int.zero) -> 
    get els eid = Some (m,wl) ->
    tickchange t st els st' els.

Inductive tickstep': TcbMod.map -> EcbMod.map -> TcbMod.map -> EcbMod.map -> TcbMod.map -> Prop :=
  endtls_step : forall (tls:TcbMod.map) (qls : EcbMod.map),
                  tickstep' tls qls tls qls emp
  | ext_step : forall (tls tls' tls'' : TcbMod.map)
                 (els els' els'' : EcbMod.map) (t : tidspec.A) 
                 (p : priority) (st st' : taskstatus) 
                 (msg0 : msg) (sus0 : susstatus) tls_used tls_used',
                 TcbMod.joinsig t (p, st, msg0, sus0) tls_used' tls_used ->
                 tickchange t st els st' els' ->
                 set tls t (p, st', msg0, sus0) = tls' ->
                 tickstep' tls' els' tls'' els'' tls_used'->
                 tickstep' tls els tls'' els'' tls_used.

Definition tickstep tls els tls' els' := tickstep' tls els tls' els' tls.

Definition tickisr_spec (vl: vallist) (O : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O') =>
  exists tls els tm,
    exists tls' els' tm',
       get O abstcblsid = Some (abstcblist tls) /\
       get O absecblsid = Some (absecblist els)/\
       get O ostmid = Some (ostm tm) /\
      O'= Some 
      ( set ( set ( set O absecblsid (absecblist els')) abstcblsid (abstcblist tls'))
      ostmid (ostm tm')) /\
      tm'=(Int.add tm Int.one)/\
      tickstep tls els tls' els'/\
      opv = None
  end.

Definition tickisr :=
  tickisr_spec (|nil|);; (isched ;; END None ?? END None).

(* task *)


(* task create *)


(*  TASKCRE *)

Definition taskcre_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr PRIO_ERR))) /\
      O2= Some O1 /\
      (exists v1 v2 v3,
         vl= (v1::v2::(Vint32 v3)::nil)/\
         Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true
      )
  end.

Definition taskcre_err_prio_already_exists (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_EXIST))) /\
      O2=Some O1 /\
      (
        exists v1 v2 v3,
          vl= (v1::v2::(Vint32 v3)::nil)
          (* cannot describe vholder
            exists tls,
              get O1 abstcblsid = Some (abstcblist tls) /\
              (exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg)) 
          *)
      )
  end.


Definition taskcre_err_no_more_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_MORE_TCB))) /\
      O2=Some O1
  end.

Definition taskcre_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      exists v1 v2 v3,
      vl= (v1::v2::(Vint32 v3)::nil)/\
          (
            opv = None /\
            Int.lt (Int.repr 63) v3 = false /\ 
            exists tls,
              OSAbstMod.get O1 abtcblsid = Some (abstcblist tls) /\
              (~ exists t' st msg sus, TcbMod.get tls t'= Some (v3,st,msg,sus)) /\
              exists tls' t' sus',
                TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull, sus')) tls'/\
                O2= Some (OSAbstMod.set O1 abtcblsid (abstcblist tls'))
          )
  end.


Definition scrt (vl : vallist) :=
  match vl with
    | v1 :: v2 :: (Vint32 v3) :: nil => spec_crt v1 v2 (Vint32 v3)
    | _ => spec_done None
  end.

Definition taskcrecode (vl : vallist) :=
  taskcre_err_prio_invalid (|vl|) ??
  taskcre_err_prio_already_exists (|vl|) ??
  taskcre_err_no_more_tcb (|vl|) ??
  (scrt vl ;; (* taskcre_succ  (|vl|) ;;  *)isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).

Definition taskcreapi:=(taskcrecode,(Tint8, Tptr Tvoid ::Tptr Tvoid::Tint8::nil)).


(* task delete *)

Definition taskdel_err_prio_is_idle (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) /\
      O2=Some O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true  
          (* Int.eq (Int.repr OS_PRIO_SELF) v3 =  true  (* /\ current is idle *) *)
         )
      )
  end.


Definition taskdel_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2=Some O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true 
         (* Int.eq (Int.repr OS_PRIO_SELF) v3 = false *)
      )
  end.

 (* placeholder or null *)
Definition taskdel_err_no_such_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) /\
      O2=Some O1 /\
      (
        exists v3,
          vl= ((Vint32 v3)::nil) /\
          (exists tls,
             get O1 abstcblsid = Some (abstcblist tls) /\
             (~ exists tid st msg sus, TcbMod.get tls tid= Some (v3, st, msg, sus)) 
          )
      )
  end.

Definition taskdel_err_is_some_mutex_owner (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER))) /\
      O2=Some O1 /\
      (
        exists v3,
          vl= ((Vint32 v3)::nil) /\
          (exists tls els eid tid t m opr wls pr sus,
             get O1 abstcblsid = Some (abstcblist tls) /\
             get O1 absecblsid = Some (absecblist els) /\
             get tls tid = Some (v3, t, m, sus) /\
             get els eid = Some (absmutexsem pr (Some (tid, opr)), wls) 
          )
      )
  end.

Definition taskdel_err_has_no_next (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) /\
      O2=Some O1 
  end.

Definition isWait4Ecb x t :=
      x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t.


Definition taskdel_clear_waitls_bit (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      exists v3,
      vl= (Vint32 v3)::nil/\
          (
            opv = None /\
            exists tls els tid eid st msg ehb wl els' t,
              exists sus,
              get O1 abtcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
              get tls tid = Some (v3, wait st t, msg, sus) /\
              isWait4Ecb st eid /\
              get els eid = Some (ehb, wl) /\
              els' = set els eid (ehb, (remove_tid tid wl)) /\
              O2= Some (set O1 absecblsid (absecblist els'))
          )
  end.


Definition sdel (vl : vallist) :=
  match vl with
    | (Vint32 v3) :: nil => spec_del (Vint32 v3)
    | _ => spec_done None
  end.

Definition taskdelcode (vl : vallist) :=
  taskdel_err_prio_invalid (|vl|)
                           ?? taskdel_err_no_such_tcb (|vl|)
                           ?? taskdel_err_prio_is_idle (|vl|)
                           ?? taskdel_err_is_some_mutex_owner  (|vl|)
                           ??  taskdel_err_has_no_next (|vl|)
                           ?? (sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR))))
                           ?? ( taskdel_clear_waitls_bit (|vl|) ;; sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).

Definition taskdelapi:=(taskdelcode,(Tint8, Tint8::nil)).

(* suspend *)

Definition tasksuspend_err_prio_is_idle (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE))) /\
      O2=Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true)
      )
  end.

Definition tasksuspend_err_prio_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2=Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true
      )
  end.

Definition tasksuspend_err_no_such_tcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO))) /\
      O2=Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (~ exists tid st msg sus, TcbMod.get tls tid = Some (v3, st, msg, sus))
        )
      )
  end.

Definition tasksuspend_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (exists tid st msg sus,
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            O2 = Some(set O1 abstcblsid (abstcblist (TcbMod.set tls tid (v3, st, msg, true))))
          )
        )
      )
  end.

Definition tasksuspendcode (vl: vallist) :=
  tasksuspend_err_prio_is_idle (|vl|) ??
  tasksuspend_err_prio_invalid (|vl|) ??
  tasksuspend_err_no_such_tcb (|vl|) ??
  (* TODO: distinguish between self and non-self cases. *)
  (tasksuspend_succ (|vl|) ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).

Definition tasksuspendapi :=
  (tasksuspendcode, (Tint8, Tint8::nil)).

Definition taskresume_err_prio_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true \/ Int.eq (Int.repr OS_LOWEST_PRIO) v3 = true)
      )
  end.
  
Definition taskresume_err_no_such_tcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_RESUME_PRIO))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (~ exists tid st msg sus, TcbMod.get tls tid = Some (v3, st, msg, sus))
        )
      )
  end.

Definition taskresume_err_not_suspended(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_NOT_SUSPENDED))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (exists tid st msg, TcbMod.get tls tid = Some (v3, st, msg, false))
        )
      )
  end.

Definition taskresume_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (exists tid st msg sus,
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            O2 = Some (set O1 abstcblsid (abstcblist (TcbMod.set tls tid (v3, st, msg, false))))
          )
        )
      )
  end.

Definition taskresumecode (vl: vallist) :=
  taskresume_err_prio_invalid (|vl|) ??
  taskresume_err_no_such_tcb (|vl|) ??
  taskresume_err_not_suspended (|vl|) ??
  (taskresume_succ (|vl|) ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).
  
Definition taskresumeapi :=
  (taskresumecode, (Tint8, Tint8::nil)).

(*interrupts*)
Definition usernmi_isr_spec (vl: vallist) (O : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O') => Some O = O'/\
      opv = None
  end.
Definition usernmi_isr := usernmi_isr_spec  (|nil|);; (isched ;; END None ?? END None).

Definition userisr_spec  (vl: vallist) (O : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O') => Some O = O'/\
      opv = None
  end.
Definition userisr := userisr_spec  (|nil|);; (isched ;; END None ?? END None).

Definition ipcisr_spec  (vl: vallist) (O : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O') => Some O = O'/\ opv = None
  end.
Definition ipcisr := ipcisr_spec  (|nil|);; (isched ;; END None ?? END None).

Definition picMin : int := Int.repr 3.     
Definition picMax : int := Int.repr 16.  

Definition int_enable_pic_absop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists v er,
          vl = ((Vint32 v) :: nil) /\ 
          (Int.ltu picMin v = true) /\ (Int.ltu v picMax = true) /\
          get O1 ierid = Some (hier er) /\
          opv = None /\ O2 = Some (set O1 ierid (hier (ierupd er (Z.to_nat (Int.unsigned v)) true)))
  end.

Definition enablepiccode (vl : vallist):= (int_enable_pic_aop(|nil|);;END None).

Definition enablepicapi:=(enablepiccode,(Tvoid,(Tint16::nil))).

Definition int_disable_pic_absop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists v er,
          vl = ((Vint32 v) :: nil) /\ 
          (*(Int.ltu picMin v = true) /\ (Int.ltu v picMax = true) /\*)
          get O1 ierid = Some (hier er) /\
          opv = None /\ O2 = Some (set O1 ierid (hier (ierupd er (Z.to_nat (Int.unsigned v)) false)))
  end.

Definition disablepiccode (vl : vallist):= (int_disable_pic_aop(|nil|);;END None).

Definition disablepicapi:=(disablepiccode,(Tvoid,(Tint16::nil))).

Definition levelMin : int := Int.repr 15.     (*0x000f*)
Definition levelMax : int := Int.repr 65521.  (*0xfff1 = 65521*)

Definition int_unlock_absop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists v er,
          vl = ((Vint32 v) :: nil) /\ 
          (Int.ltu levelMin v = true) /\ (Int.ltu v levelMax = true) /\
          get O1 ierid = Some (hier er) /\
          opv = None /\ O2 = Some (set O1 ierid (hier (ierupds er (Int.unsigned v))))
  end.

Definition unlockcode (vl : vallist):= (int_unlock_aop(|nil|);;END None).

Definition unlockapi:=(unlockcode,(Tvoid,(Tint16::nil))).

Definition int_lock_absop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists level,
          vl = nil /\
          (*get O1 ierid = Some (hier er) /\ 
          level = getLevel er intStart Int.zero intStartInt /\*)
          opv = Some (level) /\
          O2 = Some O1
          (*O2 = set O1 ierid (hier empier)*)
  end.

Definition lockcode (vl : vallist):= int_lock_aop(|nil|).

Definition lockapi:=(lockcode,(Tvoid,(Tint16::nil))).

(* exception_handler set *)

Definition exchandler_set (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      exists exchandler vl',
        (*vl = ((Vint32 exchandler)::nil)*)
        vl = ((Vint32 exchandler):: vl')/\
        (
          exists oldhandler,
            get O1 exchandlerid = Some (hexchandler oldhandler) /\
          opv = (Some (Vint32 oldhandler)) /\ 
          O2 = Some (set O1 exchandlerid (hexchandler exchandler))
        )
  end.
Definition exchandler_setcode (vl : vallist):= exchandler_set(|vl|).
Definition exchandler_setapi:=(exchandler_setcode,(Tint32,(Tint32::nil))).

Definition vecMin : int32 := Int.repr 5.     
Definition vecMax : int32 := Int.repr 15.

(* unstall handler *)
Definition unstall_fail (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists vec,
        nth_val 0 vl = Some (Vint32 vec) /\
        (*((Int.ltu vec vecMin = true) \/ (Int.ltu vecMax vec = true)) /\*)
        opv = Some (Vint32 (Int.repr ENIVAL)) /\ 
        O2 = Some O1
  end.

Definition unstall_6678_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists i vl' inthandler newinthandler,
        vl = ((Vint32 i)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (*newinthandler = (fun (x : int32) => if Int.eq x (i -ᵢ vecMin) then Int.zero else inthandler x) /\ *)
        (forall x, if Int.eq x i then newinthandler x = Int.zero else newinthandler x = inthandler x) /\
        (*update_nth_val (Z.to_nat (Int.unsigned (i -ᵢ vecMin))) (HinthandlerToListval inthandler) (V$ 0) = HinthandlerToListval newinthandler /\*)
        O2 = Some (set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

Definition unstall_handler_6678code (vl : vallist) :=
  unstall_fail (|vl|) ?? unstall_6678_succ (|vl|).
Definition unstall_handler_6678api:=(unstall_handler_6678code,(Tint32,Tint8::nil)).

Definition unstall_6713_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists i vl' inthandler newinthandler,
        vl = ((Vint32 i)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (forall x, if Int.eq x i then newinthandler x = Int.zero else newinthandler x = inthandler x) /\
        O2 = Some (set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

Definition unstall_handler_6713code (vl : vallist) :=
  unstall_fail (|vl|) ?? (int_disable_pic_aop(|nil|) ;; unstall_6713_succ (|vl|)).

Definition unstall_handler_6713api:=(unstall_handler_6713code,(Tint32,Tint8::nil)).

(* install handler *)
Definition install_fail (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        (*exists vec,
        nth_val 0 vl = Some (Vint32 vec) /\ *)
        opv = Some (Vint32 (Int.repr ENIVAL)) /\ 
        O2 = Some O1
  end.

Definition install_handler_6713_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists vl' i prio handler param eventID inthandler newinthandler,
        vl = ((Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) /\
        O2 = Some(set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

(*Definition install_handler_6713code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6713_succ(|vl|) ;; install_handlerParam_6713_succ (|vl|)).*)

Definition install_handler_6713code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6713_succ(|vl|)).

Definition install_handler_6713api:=(install_handler_6713code,(Tint32,Tint32::Tint32::Tint32::(Tptr Tvoid)::Tint32::nil)).


(*Definition install_fail (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        (*exists vec,
        nth_val 0 vl = Some (Vint32 vec) /\ *)
        opv = Some (Vint32 (Int.repr ENIVAL)) /\ 
        O2 = Some O1
  end.*)

Definition install_handler_6678_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists vl' i prio handler param eventID inthandler newinthandler,
        vl = ((Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) /\
        O2 = Some(set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

Definition install_handler_6678code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6678_succ(|vl|)).

Definition install_handler_6678api:=(install_handler_6678code,(Tint32,Tint32::Tint32::Tint32::(Tptr Tvoid)::Tint32::nil)).

