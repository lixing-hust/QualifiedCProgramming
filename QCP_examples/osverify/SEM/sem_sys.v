
(*
We instrument some of the abstraction operations of the semaphore functions
to update the recorded number of P's, V's, etc. 
 *)

Require Import NPeano.
Require Export memory.
Require Export code_notations. 
Require Export sem_language.
Require Export aux_notations. 
Require Export sem_opsem.

Open Scope list_scope.
Open Scope code_scope. 
Open Scope Z_scope.

Section UserSpace. 
  Parameter userAddrStart : addrval. 
  Parameter userAddrEnd : addrval.  
End UserSpace. 

Definition OS_LOWEST_PRIO := 63%Z.
Definition OS_IDLE_PRIO := OS_LOWEST_PRIO.

Definition OS_NO_ERR := 0%Z.
Definition OS_ERR_EVENT_TYPE := 1%Z.
Definition OS_ERR_PEND_ISR := 2%Z.
Definition OS_ERR_POST_NULL_PTR :=3%Z.
Definition OS_ERR_PEVENT_NULL := 4%Z.
Definition OS_ERR_TASK_WAITING := 8%Z.
Definition OS_TIMEOUT := 10%Z.

Parameter OS_MAX_EVENTS: Z.
Parameter CORENUM: Z. 

Definition OS_USER_MAX_EVENTS :=(OS_MAX_EVENTS-CORENUM*2)%Z.

Definition SEM_BINARY := 1%Z. 
Definition SEM_COUNTING := 2%Z.

Definition SEM_VALUE_MAX := 65535%Z.

Definition OS_SEM_OVF := 50%Z.

Parameter vhold_addr: addrval. 

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.

Definition in_rtbl (st:taskstatus):=
  match st with
  | rdy => True
  | wait x t_opt =>
      match t_opt with
      | Some time => if Int.eq time Int.zero then True else False
      | None => False
      end
  end.

Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
 (exists tls prio st msg sus,
    get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio,st,msg,sus) /\ sus=false /\ in_rtbl st/\
    forall i prio' st' msg' sus',i <> t -> get tls i = Some (prio',st',msg',sus') -> sus'=false -> in_rtbl st'-> 
              Int.ltu prio prio'=true).

Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) := 
  In t wl /\ 
  exists p st msg sus,
    get tls t = Some (p,st,msg,sus)/\
    forall t', t<>t' -> In t' wl -> exists p' st' msg' sus', get tls t' = Some (p',st',msg',sus') /\ (Int.ltu p p' = true)%Z.

Definition nsc (O : osabst) (_: LAuxSt) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) (_: LAuxSt) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; Sched) ?? (ASSUME nsc).

Definition pend_asrt vl := (fun lau => lau = {| tskpt := PtPend (nth 0 vl Vnull) |}). 
Definition isched_pt vl :=
  (spec_assume (pend_asrt vl) sc;; (sched (pend_asrt vl)))
    ?? (spec_assume (pend_asrt vl) nsc).

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
        exists els n wls ni ns1 na1 ns0 na0 gaump gaump',
          opv = (Some (Vint32 n)) /\
            get O1 absecblsid = Some (absecblist els) /\
            get els sid = Some (abssem n, wls) /\
            Int.ltu Int.zero n = true /\
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump sid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump sid {| ninit:=ni; nsig1:=ns1; nacq1:=S na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            (v' = Vint32 n /\ 
               O_opt = Some
                         (set
                            (set O1 absecblsid
                               (absecblist (set els sid (abssem (Int.sub n Int.one), wls))))
                            gauxstid (gauxst gaump')
                         )
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
        vl = (rv :: nil) /\
        opv = Some Vnull /\
        ((rv = Vnull /\ O_opt = Some O1) \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition semcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists n v' t,
        vl = ((Vint32 n) :: v' :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        opv = Some Vnull /\
        get O1 curtid = Some (oscurt t) /\ 
        (v'= Vnull /\ O_opt = Some O1  \/ v' <> Vnull /\ O_opt = None) 
  end.

Definition semcre_ecb_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
      exists v' sls sid t,
      vl = (v' :: nil) /\
        opv = None /\
        get O1 absecblsid = Some (absecblist sls) /\
        get sls sid = None /\
        get O1 curtid = Some (oscurt t) /\
        ((v' = Vptr sid /\ O_opt = Some O1) \/ v' <> Vptr sid /\ O_opt = None )
  end. 

Definition gau_init (n: int) : GAuxSt :=
  {| ninit:=n; nsig1:=0; nacq1:=0; nsig0:=0; nacq0:=0 |}. 
                 
Definition semcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists n sid sls t O' gaump gaump',
      vl = ((Vint32 n) :: (Vptr sid) :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        opv = Some (Vptr sid) /\
        get O1 absecblsid = Some (absecblist sls) /\
        get sls sid = None /\
        get O1 curtid = Some (oscurt t) /\
        get O1 gauxstid = Some (gauxst gaump) /\ 
        gaump' = set gaump sid (gau_init n) /\ 
        O' = (set (set O1 absecblsid (absecblist (set sls sid (abssem n, nil)))) gauxstid (gauxst gaump')) /\
        O_opt = Some O'
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
             exists els n wls ni ns1 na1 ns0 na0 gaump gaump',
               get O1 absecblsid = Some (absecblist els) /\
                 Int.ltu Int.zero n = true /\
                 get els qid = Some (abssem n, wls) /\
                 opv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
                 get O1 gauxstid = Some (gauxst gaump) /\ 
                 get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
                 gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=S na1; nsig0:=ns0; nacq0:=na0 |} /\ 
                 (k = Vint32 (Int.repr OS_NO_ERR)  
                  /\ O_opt = Some (set (set O1 absecblsid
                                          (absecblist (set els qid (abssem (Int.sub n Int.one), wls)))) gauxstid (gauxst gaump'))
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
            qls'=set qls qid (abssem Int.zero, t::wl) /\
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
          exists tls t p m sus els,
          exists gaump gaump' ni ns1 na1 ns0 na0,
            get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
              get O1 absecblsid = Some (absecblist els) /\ 
              get tls t = Some (p, rdy, m, sus) /\
              rv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
              get O1 gauxstid = Some (gauxst gaump) /\ 
              get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
              gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=S na0 |} /\ 
              (k = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some (set O1 gauxstid (gauxst gaump'))
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
    ?? (spec_atm (sem_pend_block (|vl|);; spec_set_pt (PtPend (nth 0 vl Vnull))) ;;
           isched_pt vl ;;
           (pend_asrt vl) # sem_pend_after_sched [| vl |] ;;
           ((spec_atm (
                 (pend_asrt vl) # sem_pend_timeout_err_rdy [| vl |];; 
                 spec_set_pt PtNormal)) ??
              (spec_atm (
                   (pend_asrt vl) # sem_pend_block_get_succ [| vl |];; 
                   spec_set_pt PtNormal)))).  


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
      exists posv, 
        get semifo posv = Some (infotid qid, Int.one) /\ O2 = None
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
        exists gaump gaump' ni ns1 na1 ns0 na0, 
          get O1 abstcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            (GetHWait tls wl t') /\
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            get tls t' = Some (p, st, m, sus) /\
            v' = (Vint32 (Int.repr OS_NO_ERR)) /\
            tls' = set tls t' (p, rdy, Vnull, sus) /\ 
            els' = set els qid (abssem n, (remove_tid t' wl)) /\
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=S ns0; nacq0:=na0 |} /\ 
            O2 = Some (set (set (set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist els')) gauxstid (gauxst gaump'))
  end.

Definition sem_post_ex_wt_abt (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls wl n, 
          get O1 abstcblsid = Some (abstcblist tls) /\
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
        exists els n wls gaump gaump' ni ns1 na1 ns0 na0,
          get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wls)) /\
            Int.ltu n (Int.repr 65535) = true /\
            opv = (Some (Vint32 (Int.repr OS_NO_ERR ))) /\
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump qid {| ninit:=ni; nsig1:=S ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            (v' = (Vint32 (Int.repr OS_NO_ERR)) /\ 
               O2 = Some (
                        set
                          (set O1 absecblsid
                             (absecblist (set els qid (abssem (Int.add n Int.one), wls))))
                          gauxstid (gauxst gaump')) \/
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
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semtrywait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo e tp,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp) /\
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
      exists v' posv semifo e tp t,
      vl = ((Vint32 posv) :: v' :: nil) /\ 
        ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
           Int.ltu posv (Int.repr 6) = true) /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (e, tp) /\
        get O1 curtid = Some (oscurt t) /\
        ((e = infonull /\ v' = Vnull) 
         /\ O_opt = Some O1)
      \/ (v' <> Vnull /\ O_opt = None) 
  end.

Definition semtrywait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp) /\
          get O1 curtid = Some (oscurt t) /\
          (v' = Vptr eid /\ O_opt = Some O1 \/ (v' <> Vptr eid /\ O_opt = None)) 
  end.

Definition semtrywait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp) /\
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
    exists v t v',
    vl = (Vint32 v) :: v' :: nil /\
    Int.ltu Int.zero v = true /\
    get O1 curtid = Some (oscurt t) /\
    (v' = Vint32 (Int.zero) /\ opv = Some v' /\ O_opt = Some O1 
     \/ v' <> Vint32 (Int.zero) /\ O_opt = None)
  end.

Definition semtrywait_after_acc_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.ltu Int.zero v = false /\
        get O1 curtid = Some (oscurt t) /\
        (v' = Vint32 (Int.mone) /\ opv = Some v' /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.mone) /\ O_opt = None)
  end.

(* H: EX vl', semtrywait ((rev vl) ++ vl') *)
(* vl = v1 :: v2 :: v3 :: v4 :: nil *) 
Definition semtrywait (vl: vallist) :=
  match vl with
    vsm :: v1 :: v20 :: v2 :: v3 :: v4 :: nil => 
      (semtrywait_semerr (| vsm::v1::nil |) ?? semtrywait_sem_pos (| vsm::v1::nil |));; 
      (semtrywait_poserr (| v1::v4::nil |) ??  
         (semtrywait_get_ecb_ptr (| v1::v20::nil |);; 
          (semtrywait_if_null_yes (| v20::v4::nil |) ?? 
             (semtrywait_if_null_no (| v20::nil |);;
              (semtrywait_get_ecb_ptr1 (| v1::v2::nil |) ?? semtrywait_get_ecb_ptr2 (| v1::v2::nil |) ??
               semtrywait_ecb_ptr_holder_abt (| v1::v2::nil |));;  
              semacc (v2::v3::nil);;
              (semtrywait_after_acc_1 (| v3::v4::nil |) ??
                 semtrywait_after_acc_2 (| v3::v4::nil |))))))
  | _ => spec_abort
  end.

Definition semtrywaitapi := (semtrywait, (Tint32, Tptr sem_t::nil)).


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
      exists posv semifo, 
      vl = (posv :: nil) /\
       get O1 seminfoid = Some (seminfo semifo) /\
      (
      ((~(exists pos tp, get semifo pos = Some (infonull, tp) /\ 
                         (0 <= (Int.unsigned pos) < (OS_USER_MAX_EVENTS / 3))%Z) /\
          posv = Vint32 (Int.repr 255)) \/
       (exists pos tp, get semifo pos = Some (infonull, tp) /\
         posv = Vint32 pos )) /\ O_opt = Some O1
      ) \/
      (
      ((~(exists pos tp, get semifo pos = Some (infonull, tp) /\ 
                         (0 <= (Int.unsigned pos)  < (OS_USER_MAX_EVENTS / 3))%Z) /\
      posv <> Vint32 (Int.repr 255)) \/
     (exists pos tp, get semifo pos = Some (infonull, tp) /\
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
    exists pos semifo e tp,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp) /\
      opv = None /\
      O_opt = Some (set O1 seminfoid (seminfo (set semifo pos (infohold, tp))))
  end.

Definition seminit_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t semifo e tp semifo',
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp) /\
      get O1 curtid = Some (oscurt t) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr /\ semifo' = set semifo pos (infotid eid, tp))) 
       \/ eptr = Vnull /\ semifo' = set semifo pos (infonull, tp))
      /\  
        O_opt = Some (set O1 seminfoid (seminfo semifo'))
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
      exists pos e semifo tp semifo', 
      vl = (Vint32 pos) :: nil /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp) /\ 
      opv = None /\
      semifo' = set semifo pos (e, (Int.repr SEM_COUNTING)) /\
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
    vsm :: value :: posv :: vr_cre :: nil => 
      seminit_iserr (| nil |) ??
      seminit_semerr (| vsm :: nil |) ??
        seminit_valerr (| value :: nil |) ??
        (seminit_pos (| posv :: nil |);;
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
      exists pos e semifo tp semifo', 
      vl = (Vint32 pos) :: nil /\
      get O1 seminfoid = Some (seminfo semifo) /\
      get semifo pos = Some (e, tp) /\ 
      opv = None /\
      semifo' = set semifo pos (e, (Int.repr SEM_BINARY)) /\
      O_opt = Some (set O1 seminfoid (seminfo semifo')) 
  end.

(* H: EX vl', seminit ((rev vl) ++ vl') *)
(* vl = vsm :: value :: posv :: vr_cre :: nil *) 
Definition seminitbin (vl: vallist) :=
  match vl with
    vsm :: value :: posv :: vr_cre :: nil => 
      seminit_iserr (| nil |) ??
      seminit_semerr (| vsm :: nil |) ??
        seminit_valerr (| value :: nil |) ??
        (seminit_pos (| posv :: nil |);;
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
       Int.ltu (Int.repr 6) posv = true \/ Int.eq posv (Int.repr 6) = true) /\  
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
       Int.ltu posv (Int.repr 6) = true) /\    
      exists semeibs tp,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infonull, tp) /\ 
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
       Int.ltu posv (Int.repr 6) = true) /\    
      exists semeibs tp,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infohold, tp) /\
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
       Int.ltu posv (Int.repr 6) = true) /\    
      exists semeibs tp els n wls eid,
        get O1 seminfoid = Some (seminfo semeibs) /\
        get semeibs posv = Some (infotid eid, tp) /\
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
        exists pbls posv,
          get O1 pblsid = Some (pblist pbls) /\
            get pbls a = Some posv /\ 
            ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
               Int.ltu posv (Int.repr 6) = true) /\    
            exists semeibs semeibs' tp els n eid els' gaump gau gaump',
              get O1 seminfoid = Some (seminfo semeibs) /\
                get semeibs posv = Some (infotid eid, tp) /\
                get O1 absecblsid = Some (absecblist els) /\
                get els eid = Some (abssem n, nil) /\
                join els' (sig eid (abssem n, nil)) els /\
                get O1 gauxstid = Some (gauxst gaump) /\ 
                get gaump eid = Some gau /\
                join gaump' (sig eid gau) gaump /\ 
                semeibs' = set semeibs posv (infonull, tp) /\ 
                O_opt = Some
                          (set
                             (set
                                (set O1 absecblsid (absecblist els'))
                                seminfoid (seminfo semeibs'))
                             gauxstid (gauxst gaump'))
  end.

Definition semdestroy (vl: vallist) :=
  match vl with
    v1 :: nil => 
      semdestroy_semerr (| vl |) ??
      semdestroy_sem_nopblk_abt (| vl |) ?? 
      semdestroy_pos_err (| vl |) ??
      semdestroy_not_placeholder_assm (| vl |) ??
      semdestroy_pevent_null_err (| vl |) ??
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
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semwait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp) /\
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
      exists v' posv semifo tp t,
      vl = ((Vint32 posv) :: v' :: nil) /\ 
        ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
           Int.ltu posv (Int.repr 6) = true) /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (infonull, tp) /\
        get O1 curtid = Some (oscurt t) /\
        ((v' = Vnull /\ O_opt = Some O1)
         \/ (v' <> Vnull /\ O_opt = None)) 
  end.

Definition semwait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp) /\
          get O1 curtid = Some (oscurt t) /\
          (v' = Vptr eid /\ O_opt = Some O1 \/ (v' <> Vptr eid /\ O_opt = None)) 
  end.

Definition semwait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp) /\
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
      exists v t v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.ltu Int.zero v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        (v' = Vint32 (Int.mone) /\ opv = Some v' /\ O_opt = Some O1 
         \/ v' <> Vint32 (Int.mone) /\ O_opt = None) 
  end.

Definition semwait_after_pend_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.ltu Int.zero v = false /\
        get O1 curtid = Some (oscurt t) /\
        opv = Some (Vint32 (Int.zero)) /\
        (v' = Vint32 (Int.zero) /\ opv = Some v' /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.zero) /\ O_opt = None) 
  end.

Definition semwait_afteraddcheck (vl: vallist) :=
  match vl with
    v1 :: v20 :: v2 :: v3 :: v4 :: nil => 
      (semwait_poserr (|v1::v4::nil|) ??  
         (semwait_get_ecb_ptr (| v1::v20::nil |);; 
          (semwait_if_null_yes (| v20::v4::nil |) ?? 
             (semwait_if_null_no (| v20::nil |);;
              (semwait_get_ecb_ptr1 (| v1::v2::nil |) ?? semwait_get_ecb_ptr2 (| v1::v2::nil |) ?? 
                 semwait_ecb_ptr_holder_abt (| v1::v2::nil |) );;  
              (sem_pend (v2:: (Vint32 Int.zero) :: v3 :: nil);; 
               (semwait_after_pend_1 (|v3::v4::nil|) ??
                  semwait_after_pend_2 (|v3::v4::nil|))))))) 
  | _ => spec_abort
  end.

(* H: EX vl', semwait ((rev vl) ++ vl') *)
(* vl = vsm :: v1 :: v20 :: v2 :: v3 :: v4 :: nil *) 
Definition semwait (vl: vallist) :=
  match vl with
    vsm :: v1 :: v20 :: v2 :: v3 :: v4 :: nil => 
      (semwait_iserr (| nil |) ??
         ((semwait_semerr (| vsm::v1::nil |) ?? semwait_sem_pos (| vsm::v1::nil |) );; 
          semwait_afteraddcheck (v1 :: v20 :: v2 :: v3 :: v4 :: nil)))
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
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
       O_opt = Some O1 /\ opv = Some (Vint32 (Int.mone)) 
  end.

Definition semtimedwait_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp) /\
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
      exists v' posv semifo tp t,
      vl = ((Vint32 posv) :: v' :: nil) /\ 
        ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
           Int.ltu posv (Int.repr 6) = true) /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (infonull, tp) /\
        get O1 curtid = Some (oscurt t) /\
        (v' = Vnull /\ O_opt = Some O1) 
      \/ (v' <> Vnull /\ O_opt = None) 
  end.

Definition semtimedwait_get_ecb_ptr2 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp eid t,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infotid eid, tp) /\
          get O1 curtid = Some (oscurt t) /\
          (v' = Vptr eid /\ O_opt = Some O1 \/ (v' <> Vptr eid /\ O_opt = None))
  end.

Definition semtimedwait_ecb_ptr_holder_abt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp,
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (infohold, tp) /\
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
      exists v t, 
      vl = (Vint32 v)  :: nil /\
        Int.eq (Int.repr OS_TIMEOUT) v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1 
  end.

Definition semtimedwait_after_pend_1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t, 
      vl = (Vint32 v)  :: nil /\
        Int.ltu Int.zero v = true /\
        get O1 curtid = Some (oscurt t) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1 
  end.

Definition semtimedwait_after_pend_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t,
      vl = (Vint32 v)  :: nil /\
        Int.ltu Int.zero v = false /\
        get O1 curtid = Some (oscurt t) /\
        opv = Some (Vint32 (Int.zero)) /\
        O_opt = Some O1 
  end.

Definition semtimedwait_afteraddcheck (vl: vallist) :=
  match vl with
    vtime :: v1 :: v20 :: v2 :: v3 :: nil => 
      (semtimedwait_poserr (|v1::nil|) ?? 
         (semtimedwait_get_ecb_ptr (| v1::v20::nil |);; 
          (semtimedwait_if_null_yes (| v20::nil |) ?? 
             (semtimedwait_if_null_no (| v20::nil |);;
              (semtimedwait_timeout_err (|vtime::nil|) ?? 
                 (semtimedwait_get_ecb_ptr1 (| v1::v2::nil |) ?? semtimedwait_get_ecb_ptr2 (| v1::v2::nil |) ?? 
                    semtimedwait_ecb_ptr_holder_abt (| v1::v2::nil |) );; 
               (sem_pend (v2:: vtime :: v3 :: nil) ;; 
                (semtimedwait_after_pend_timeout (|v3::nil|) ??
                   semtimedwait_after_pend_1 (|v3::nil|) ??
                   semtimedwait_after_pend_2 (|v3::nil|) ))) )))) 
  | _ => spec_abort
  end.

Definition semtimedwait (vl: vallist) :=
  match vl with
    vsm :: vtime :: v1 :: v20 :: v2 :: v3 :: nil => 
      (semtimedwait_iserr (| nil |) ??
         ((semtimedwait_semerr (| vsm::v1::nil |) ?? semtimedwait_sem_pos (| vsm::v1::nil |) );; 
          semtimedwait_afteraddcheck (vtime :: v1 :: v20 :: v2 :: v3 :: nil)))
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
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semsignal_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv semifo e tp, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp) /\
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
    exists v' posv semifo t tp,  
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr 6) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infonull, tp) /\
    get O1 curtid = Some (oscurt t) /\
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition semsignal_get_ecb_ptr2 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo eid t tp,  
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr 6) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infotid eid, tp) /\
    get O1 curtid = Some (oscurt t) /\
    (v' = Vptr eid /\ O_opt = Some O1 \/ v' <> Vptr eid /\ O_opt = None)  
  end. 

Definition semsignal_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' posv semifo tp, 
    vl = ((Vint32 posv) :: v' :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr 6) = true) /\
    get O1 seminfoid = Some (seminfo semifo) /\
    get semifo posv = Some (infohold, tp) /\
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
      exists posv semifo e tp, 
        vl = ((Vint32 posv) :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          get semifo posv = Some (e, tp) /\ 
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
      exists rv posv semifo eid tp , 
      exists els n wl,
        vl = ((Vint32 posv) :: rv :: nil) /\
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
          get O1 seminfoid = Some (seminfo semifo) /\
          EmbMod.get semifo posv = Some (infotid eid, tp) /\
          tp = (Int.repr 1)/\
          get O1 absecblsid = Some (absecblist els) /\
          get els eid = Some (abssem n, wl) /\
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
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
    opv = Some (Vint32 Int.zero) /\  
    (v' = Vint32 (Int.zero) /\ O_opt = Some O1
     \/ v' <> Vint32 (Int.zero) /\ O_opt = None) 
  end.

Definition semsignal_after_post_2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v t v',
    vl = (Vint32 v) :: v' :: nil /\
    v <> Int.zero /\ 
    get O1 curtid = Some (oscurt t) /\
    opv = Some (Vint32 Int.mone) /\  
    (v' = Vint32 (Int.mone) /\  O_opt = Some O1
     \/ v' <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition semsignal_type_bin (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e, 
      vl = (Vint32 posv) :: nil /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (e, Int.one) /\ 
        O_opt = Some O1 /\ 
        opv = None 
  end.

Definition semsignal_type_not_bin (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv semifo e tp, 
      vl = (Vint32 posv) :: nil /\
        get O1 seminfoid = Some (seminfo semifo) /\
        get semifo posv = Some (e, tp) /\ 
        Int.eq tp Int.one = false /\ 
        O_opt = Some O1 /\ 
        opv = None 
  end.

Definition semsignal (vl: vallist) :=
  match vl with
    vsm :: v1 :: v2 :: v2' :: v3 :: v4 :: nil => 
      (semsignal_semerr (|vsm :: v1 :: nil|) ?? semsignal_sem_pos (|vsm :: v1 :: nil|));;
      (semsignal_poserr (|v1 :: v4 :: nil|)
         ??
         semsignal_get_ecb_ptr (|v1 :: v2 :: nil|);;
       (semsigna_if_null_yes (|v2 :: v4 :: nil|)
          ?? 
          semsigna_if_null_no (|v2 :: nil|);;
        ((semsignal_type_bin (| v1 :: nil |);; 
          (semsignal_get_ecb_ptr1 (| v1 :: v2' :: nil |) ?? 
             semsignal_get_ecb_ptr2 (| v1 :: v2' :: nil |) ?? 
             semsignal_ecb_ptr_holder_abt (| v1 :: v2' :: nil |));;  
          (sem_post_bin (v2' :: v3 :: nil) ;;
           (semsignal_after_post_1 (| v3 :: v4 :: nil |) ?? semsignal_after_post_2 (| v3 :: v4 :: nil |)))
            ??
            semsignal_type_not_bin (| v1 :: nil |);; 
          (semsignal_get_ecb_ptr1 (|v1 :: v2' :: nil|) ??
             semsignal_get_ecb_ptr2 (| v1 :: v2' :: nil |) ?? 
             semsignal_ecb_ptr_holder_abt (| v1 :: v2' :: nil |));;  
          (sem_post (v2' :: v3 :: nil);; 
           (semsignal_after_post_1 (|v3 :: v4 :: nil|) ?? semsignal_after_post_2 (|v3 :: v4 :: nil|))))))) 
  | _ => spec_abort
  end. 
  
Definition semsignalapi := (semsignal, (Tint32, Tptr sem_t::nil)).  


(* (* (****************************** sem_flush ************************************) *) *)

(* Definition semflush_iserr *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       vl = nil /\ *)
(*         opv = Some (Vint32 (Int.mone)) /\ *)
(*         O_opt = Some O1 *)
(*   end. *)

(* Definition semflush_semerr *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists vsem, *)
(*       vl = vsem :: nil /\ *)
(*         (vsem = Vnull \/ *)
(*            exists a, *)
(*              vsem = Vptr a /\  *)
(*                (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true) *)
(*         ) /\  *)
(*         opv = Some (Vint32 (Int.mone)) /\ *)
(*         O_opt = Some O1 *)
(*   end. *)

(* Definition semflush_sem_pos *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists a v', *)
(*       vl = (Vptr a) :: v' :: nil /\ *)
(*         cmpaddr Clt userAddrStart a = true /\ *)
(*         cmpaddr Cle a userAddrEnd = true /\ *)
(*         (~(exists i, v' = Vint32 i) /\ O_opt = None \/ *)
(*            exists pbls,  *)
(*            get O1 pblsid = Some (pblist pbls) /\ *)
(*              opv = None /\ *)
(*              ((exists posv, *)
(*                   (get pbls a = Some posv /\ *)
(*                   (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None))) *)
(*                 \/ get pbls a = None /\ O_opt = None)) *)
(*   end. *)

(* Definition semflush_poserr  *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv,  *)
(*       vl = ((Vint32 posv) :: nil) /\  *)
(*         (Int.ltu posv Int.zero = true \/ *)
(*            Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\ *)
(*       opv = Some (Vint32 (Int.mone)) /\ *)
(*       O_opt = Some O1 *)
(*   end. *)

(* Definition semflush_get_ecb_ptr  *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists v' posv semifo e tp,  *)
(*         vl = ((Vint32 posv) :: v' :: nil) /\  *)
(*           ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\ *)
(*              Int.ltu posv (Int.repr 6) = true) /\ *)
(*           get O1 seminfoid = Some (seminfo semifo) /\ *)
(*           get semifo posv = Some (e, tp) /\ *)
(*           (((exists eid, e = infotid eid /\ v' = Vptr eid) \/ e = infonull /\ v' = Vnull) *)
(*            /\ O_opt = Some O1 *)
(*            \/ *)
(*              (((~exists eid, e = infotid eid) /\ e <> infonull) \/  *)
(*                 ((exists eid, e = infotid eid /\ v' <> Vptr eid) \/ e = infonull /\ v' <> Vnull)) *)
(*              /\ O_opt = None) *)
(*   end. *)

(* Definition semflush_if_null_yes *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       (vl = Vnull  :: nil) /\ *)
(*         opv = Some (Vint32 (Int.mone)) /\  *)
(*         O_opt = Some O1 *)
(*   end.  *)

(* Definition semflush_if_null_no *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists eid, *)
(*       (vl = Vptr eid :: nil) /\ *)
(*         opv = None /\ *)
(*         O_opt = Some O1 *)
(*   end.  *)

(* Definition semflush_get_not_hold *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo e tp,  *)
(*         vl = ((Vint32 posv) :: nil) /\  *)
(*           get O1 seminfoid = Some (seminfo semifo) /\ *)
(*           get semifo posv = Some (e, tp) /\ *)
(*           opv = None /\ *)
(*           (((exists eid, e = infotid eid ) \/ e = infonull) *)
(*            /\ O_opt = Some O1 *)
(*            \/ *)
(*              ((~exists eid, e = infotid eid) /\ e <> infonull) *)
(*              /\ O_opt = None) *)
(*   end. *)

(* Definition semflush_type_err *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo eid tp els, *)
(*       (vl = Vint32 posv :: nil) /\ *)
(*         opv = Some (Vint32 (Int.mone)) /\  *)
(*          get O1 seminfoid = Some (seminfo semifo) /\ *)
(*           get O1 absecblsid = Some (absecblist els) /\ *)
(*          get semifo posv = Some (infotid eid, tp) /\ *)
(*          ~(exists n wl, get els eid = Some (abssem n, wl)) /\ *)
(* (*          Int.eq tp (Int.repr OS_EVENT_TYPE_SEM) = false /\ *) *)
(*         O_opt = Some O1 *)
(*   end.  *)

(* Definition semflush_get_valid_ecb *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo e tp,  *)
(*         vl = ((Vint32 posv) :: nil) /\  *)
(*           get O1 seminfoid = Some (seminfo semifo) /\ *)
(*           get semifo posv = Some (e, tp) /\ *)
(*           opv = None /\ *)
(*           ((exists eid, e = infotid eid ) /\ O_opt = Some O1 *)
(*            \/ *)
(*              ((~exists eid, e = infotid eid)/\ O_opt = None)) *)
(*   end. *)

(* Definition semflush_null *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo tp, *)
(*       (vl = Vint32 posv :: nil) /\ *)
(*         opv = None /\  *)
(*          get O1 seminfoid = Some (seminfo semifo) /\ *)
(*          get semifo posv = Some (infonull, tp) /\ *)
(*         O_opt = Some O1 *)
(*   end.  *)

(* Definition semflush_no_wl *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo eid tp els n, *)
(*       (vl = Vint32 posv :: nil) /\ *)
(*         opv = None /\  *)
(*          get O1 seminfoid = Some (seminfo semifo) /\ *)
(*           get O1 absecblsid = Some (absecblist els) /\ *)
(*          get semifo posv = Some (infotid eid, tp) /\ *)
(*          get els eid = Some (abssem n, nil) /\ *)
(*         O_opt = Some O1 *)
(*   end.  *)

(* Fixpoint set_tls_rdy (wl: list addrval) (tls: TcbMod.map) : TcbMod.map := *)
(* match wl with *)
(*  | nil => tls *)
(*  | tid :: wl' => match TcbMod.get tls tid  with  *)
(*                             | None => set_tls_rdy wl' tls *)
(*                             | Some (p, st, m, sus) => set_tls_rdy wl' (set tls tid (p,rdy,Vnull, sus)) *)
(*                             end *)
(* end. *)

(* Definition semflush_set_wl_all_rdy *)
(*   (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists posv semifo eid tp els n wl tls tls', *)
(*       (vl = Vint32 posv :: nil) /\ *)
(*         opv = None /\  *)
(*          get O1 seminfoid = Some (seminfo semifo) /\ *)
(*          get O1 absecblsid = Some (absecblist els) /\ *)
(*          get O1 abstcblsid = Some (abstcblist tls) /\ *)
(*          get semifo posv = Some (infotid eid, tp) /\ *)
(*          get els eid = Some (abssem n, wl) /\  *)
(*          wl <> nil /\ *)
(*          tls' = set_tls_rdy wl tls /\ *)
(*         O_opt = Some (set (set O1 absecblsid (absecblist (set els eid (abssem n, nil)))) abstcblsid (abstcblist tls')) *)
(*   end. *)

(* Definition semflush (vl: vallist) := *)
(*   match vl with *)
(*     V_sem :: V_pos :: V_pevent :: nil =>  *)
(*       semflush_iserr (| nil |) ?? *)
(*       (semflush_semerr (| V_sem :: nil |) ?? *)
(*          (semflush_sem_pos (| V_sem :: V_pos :: nil |) ;; *)
(*             (semflush_poserr (| V_pos :: nil |) ?? *)
(*                 (semflush_get_ecb_ptr (| V_pos :: V_pevent :: nil |) ;; *)
(*                   (semflush_if_null_yes (| V_pevent :: nil |) ??  *)
(*                     (semflush_if_null_no (| V_pevent :: nil |) ;; *)
(*                        ((semflush_get_not_hold (| V_pos :: nil |) ;; semflush_type_err (| V_pos :: nil|)) ?? *)
(*                               (semflush_get_valid_ecb (| V_pos :: nil |) ;;  *)
(*                                 ((* semflush_null (| V_pos :: nil |) ?? *) semflush_no_wl (| V_pos :: nil |) ?? *)
(*                                   semflush_set_wl_all_rdy (| V_pos :: nil|)) ;; isched ;; (END (Some (Vint32 Int.zero))))))))) ))  *)
(*   | _ => spec_abort *)
(*   end. *)

(* Definition semflushapi := (semflush, (Tint32, Tptr sem_t :: nil)). *)





Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Definition int_spec_list : list (hid * int_code) := nil .

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec  := convert_int_spec int_spec_list.

Definition sem_trywait := 282%Z.
Definition sem_init := 288%Z.
Definition sem_init_bin := 295%Z.
Definition sem_destroy := 296%Z.
Definition sem_wait := 297%Z.
Definition sem_timedwait := 298%Z.
Definition sem_signal := 299%Z. 
Definition sem_flush := 300%Z.
Definition sem_getvalue := 301%Z.

Definition api_spec_list' := 
  (sem_trywait, semtrywaitapi)  
  :: (sem_wait, semwaitapi)  
  :: (sem_timedwait, semtimedwaitapi) 
  :: (sem_signal, semsignalapi) 
  :: (sem_init, seminitapi) 
  :: (sem_init_bin, seminitbinapi) 
  :: (sem_destroy, semdestroyapi) 
  :: nil
.

Definition api_spec':= convert_api_spec api_spec_list'.

Definition os_spec' := (api_spec', int_spec, GetHPrio).
