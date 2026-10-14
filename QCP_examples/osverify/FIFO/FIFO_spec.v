Require Import NPeano.
Require Export log_language.
Require Export log_opsem.
Require Export log_code_notations.
Require Export log_code_defs.
Require Export log_assertion.
Require Export memory.

Open Scope list_scope.
Open Scope code_scope. 
Open Scope Z_scope.

Definition mq_info_t : type := 
    STRUCT mq_info ­{
                  ⌞
                  mq_waittype @ Int32; 
                  mq_flags @ Long; 
                  mq_maxmsg @ Long;
                  mq_msgsize @ Long;
                  mq_curmsgs @ Long;
                  task_blocked @ Int8u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) 
                  ⌟
                 }­.
Definition OS_Q_DATA : type := 
    STRUCT os_q_data ­{
                  ⌞
                  OSMsg @ Void ∗; 
                  OSNMsgs @ Int16u; 
                  OSQSize @ Int16u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) ;
                  OSEventGrp @ Int8u
                  ⌟
                 }­.

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

Definition nsc (O : osabst) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc).

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
  
Fixpoint set_tls_rdy (wl: list addrval) (tls: TcbMod.map) : TcbMod.map :=
match wl with
 | nil => tls
 | tid :: wl' => match TcbMod.get tls tid  with 
                            | None => set_tls_rdy wl' tls
                            | Some (p, st, m, sus) => set_tls_rdy wl' (set tls tid (p,rdy,Vnull, sus))
                            end
end.

Fixpoint set_tls_rdy0 (wl: list addrval) (tls: TcbMod.map) : TcbMod.map :=
  match wl with
  | nil => tls
  | tid :: wl' => match TcbMod.get tls tid  with 
                  | None => set_tls_rdy0 wl' tls
                  | Some (p, _, m, sus) => set_tls_rdy0 wl' (set tls tid (p, rdy, m, sus))
                  end
  end.
  
Fixpoint Get_struct (l: (list (addrval * type * (list val))))(a: addrval) :  (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_struct l' a 
                                   end  
end.
Fixpoint Set_struct' (l: (list (addrval * type * (list val))))(a: addrval) (id : ident ) ( b : val)
     :  (list (addrval * type * (list val))):=
  match l with 
  | nil => nil  
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  =>match t with 
                                                    | Tstruct sid decls =>  match id_nth id decls  with
                                                                                               | None =>  (ad, t, vl ) :: l'
                                                                                               | Some n => ((ad, t, update_nth_val n vl b) :: l')
                                                                                                end
                                                    | _ =>  (ad, t, vl ) :: l'
                                                    end
                                   | false => ((ad, t, vl ) :: (Set_struct' l' a id b))
                                   end
end.  
Fixpoint Get_array (l: (list (addrval * nat * (list val))))(a: addrval) :  (option (addrval * nat * (list val))) :=
  match l with 
  | nil => None
  | (ad, n, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, n, vl )
                                   | false => Get_array l' a 
                                   end  
end.
Fixpoint Set_array' (l: (list (addrval * nat * (list val))))(a: addrval) (vl': list val)
     :  (list (addrval * nat * (list val))):=
  match l with 
  | nil => nil  
  | (ad, n, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => (ad, n , vl') :: l'
                                   | false => ((ad, n, vl ) :: (Set_array' l' a vl'))
                                   end
end.  
(* ucos_lib/events/mq_getinfo_pure.v *) 
Fixpoint get_tls_blocked_q_num (tls : TcbMod.rlist) (sid: addrval) :=
match tls with
| nil => 0%nat
| ( (tid,(p,st,m,sus)) :: tls') => 
        match st with
        | wait (os_stat_q eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_q_num tls' sid)
                                                                     else (get_tls_blocked_q_num tls' sid)
        | wait (os_stat_postq eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_q_num tls' sid)
                                                                     else (get_tls_blocked_q_num tls' sid)
        | _ => (get_tls_blocked_q_num tls' sid)
        end
end.
Fixpoint Int_add_n (n:nat) (vh: int32) (vadd: int32) :int32 :=
match n with
0%nat => vh
| S n' => Int.modu (Int.add (Int_add_n n' vh vadd) vadd) (Int.repr Byte.modulus)
end.
  
(***********************Q spec**************************************)

(*  qcre  *)
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

Definition tsk_normal_ev locmp ptrmp tid qid :=
  get locmp tid = Some (Vint32 (Int.repr __EvLoc_normal)) /\
  (exists muxp semp qp, 
      get ptrmp tid = Some (muxp, semp, qp) /\
      (muxp = Vptr qid \/ semp = Vptr qid \/ qp = Vptr qid)).

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
         \/ (exists t', tsk_normal_ev locmp ptrmp t' qid) /\ O_opt = None)
  end.

Definition qcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' size qid qls t locmp locmp' O' ,
    exists O'' log log' cmp ,
      vl = ((Vint32 size)  :: v' :: nil) /\
      opv = Some (Vptr qid) /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls qid = None /\
      get O1 evlocid = Some (evloc locmp) /\
      get O1 curtid = Some (oscurt t) /\   
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
      get O1 loglsid = Some ( oslog log ) /\
      log' =  log ++ ((creque qid ) :: nil) /\
      get O1 mqcntid = Some (mqcnt cmp) /\
      get cmp qid = None/\
      O'' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt (set cmp qid 0%nat ) )/\
      O' = (set O'' absecblsid (absecblist (set qls qid (absmsgq (nil:list ms) size (nil:list tid), (nil:list tid))))) /\
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
      exists posv qtls, 
      vl = (posv :: nil) /\
      opv = None /\
       get O1 absmqattrid = Some (absmqattr qtls) /\
      (
          (
          ((~(exists pos wtype flag maxm msize curm, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm) /\ 
                                                 0 <= (Int.unsigned pos) < (OS_USER_MAX_EVENTS / 3)) /\
              posv = Vint32 (Int.repr 255)) \/
           (exists pos wtype flag maxm msize curm, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm) /\
             posv = Vint32 pos )) /\ O_opt = Some O1
          ) \/
          (
          ((~(exists pos wtype flag maxm msize curm, get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm) /\ 
                                                 0 <= (Int.unsigned pos)  < (OS_USER_MAX_EVENTS / 3)) /\
          posv <> Vint32 (Int.repr 255)) \/
         (exists pos wtype flag maxm msize curm,  get qtls pos = Some ( Null, wtype, flag, maxm, msize, curm) /\
          posv <> Vint32 pos )) /\ O_opt = None
          )
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
  
(* set ECB pointer in EIB to the placeholder *)
(* update the ghost location and index to reflect the status of creating a sem. *) 
Definition mqcreate_set_placeholder
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos qtls et wtype flag maxm msize curm,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      opv = None /\
      O_opt = Some (set O1 absmqattrid (absmqattr (set qtls pos ( Holder, wtype, flag, maxm, msize, curm) )))
  end.
Parameter vhold_addr : addrval.
Definition mqcreate_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t qtls qtls' ,
    exists et wtype flag maxm msize curm,
    exists locmp locmp' ptrmp ptrmp' muxp semp qp,
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      get O1 curtid = Some (oscurt t) /\
      get O1 evlocid = Some (evloc locmp) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\
      get O1 evptrid = Some (evptr ptrmp) /\
      get ptrmp t = Some (muxp, semp, qp) /\
      ptrmp' = set ptrmp t (muxp, semp, Vnull) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr /\ qtls' = set qtls pos (Valid_Addr eid, wtype, flag, maxm, msize, curm))) 
        \/ eptr = Vnull /\ qtls' = set qtls pos (Null, wtype, flag, maxm, msize, curm)) /\  
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
      exists et wtype flag maxm msize curm,
      vl = (Vint32 pos) :: (Vint32 max_msgs) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, flag, max_msgs, msize, curm) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_msgsize
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos msg_size qtls qtls', 
      exists et wtype flag maxm msize curm,
      vl = (Vint32 pos) :: (Vint32 msg_size) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, flag, maxm, msg_size, curm) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_flags
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos mq_blockflag qtls qtls', 
      exists et wtype flag maxm msize curm,
      vl = (Vint32 pos) :: (Vint32 mq_blockflag) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      opv = None /\
      qtls' = set qtls pos ( et, wtype, mq_blockflag, maxm, msize, curm) /\
      O_opt = Some (set O1 absmqattrid (absmqattr qtls')) 
  end.

Definition mqcreate_set_waittype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos  qtls qtls', 
      exists et wtype flag maxm msize curm,
      vl = (Vint32 pos) :: nil /\
      get O1 absmqattrid = Some (absmqattr qtls) /\
      get qtls pos = Some ( et, wtype, flag, maxm, msize, curm) /\
      opv = Some (Vint32 pos) /\
      qtls' = set qtls pos ( et, (Int.repr PTHREAD_WAITQ_PRIO), flag, maxm, msize, curm) /\
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
    mq_blockflag :: max_msgs :: msg_size :: waitq_type :: posv :: rv_cre ::  rv :: nil  =>
        mqcreate_max_msgs_err (|max_msgs :: rv :: nil|) ??
        mqcreate_msg_size_err (|msg_size :: rv :: nil|) ??
        mqcreate_mq_blockflag_err (|mq_blockflag :: rv :: nil|) ??
        mqcreate_waitq_type_err (|waitq_type :: rv :: nil|) ??
        mqcreate_iserr (| nil |) ??
        (mqcreate_pos (| posv ::nil |) ;;
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

(****** qdel *********)

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

Definition qdel_succ_ex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
    exists qid,
    vl=  ((Vptr qid)::nil) /\
    (
      exists qls qls' x y pwls wls tls tls' tls'',
      exists ptrmp ptrmp' t log cmp O' log' cnt cmp',
        opv = None  /\
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
        get O1 loglsid = Some ( oslog log ) /\
        log' =  log ++ ((delque qid ) :: nil) /\
        get O1 mqcntid = Some (mqcnt cmp) /\
        get cmp qid = Some cnt /\
        join cmp' (sig qid cnt) cmp /\
        O' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt cmp') /\
        O_opt = Some (set (set (set O' absecblsid (absecblist qls')) abstcblsid (abstcblist tls'')) evptrid (evptr ptrmp'))
    )
  end.

Definition qdel_succ_nex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
    exists qid,
    vl=  ((Vptr qid)::nil) /\
    (
      exists qls qls' x y pwls wls ptrmp ptrmp' t,
      exists log log' cmp cnt O' cmp',
        opv = None  /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls qid = Some (absmsgq x y nil, nil) /\
        join qls' (sig qid (absmsgq x y pwls, wls)) qls /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get O1 curtid = Some (oscurt t) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        get O1 loglsid = Some ( oslog log ) /\
        log' =  log ++ ((delque qid ) :: nil) /\
        get O1 mqcntid = Some (mqcnt cmp) /\
        get cmp qid = Some cnt /\
        join cmp' (sig qid cnt) cmp /\
        O' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt cmp') /\
        O_opt = Some (set (set O' absecblsid (absecblist qls')) evptrid (evptr ptrmp'))
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

Definition mqdelete_mqdes_err
           (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists mqdes,
      vl= (Vint32 mqdes :: nil )/\
      (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr 6) mqdes = true \/ mqdes =(Int.repr 6)) /\
      opv = Some (Vint32 (Int.mone)) /\
      O_opt = Some O1 
  end.

Definition mqdelete_ecb_ptr_null
           (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes qeibs wtype flag maxm msize curm, 
    vl = ((Vint32 mqdes) :: nil) /\ 
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Null, wtype, flag, maxm, msize, curm) /\
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
    exists mqdes qeibs wtype flag maxm msize curm, 
    vl = ((Vint32 mqdes) :: nil) /\ 
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Holder, wtype, flag, maxm, msize, curm) /\
    opv = None /\
    O_opt = None 
  end. 

Definition mqdelete_get_set_ecb_ptr
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mqdes qeibs wtype flag maxm msize curm t eid v',
    exists qeibs' locmp ptrmp locmp' ptrmp',
    vl = ((Vint32 mqdes) :: v' :: nil) /\
    get O1 absmqattrid = Some (absmqattr qeibs) /\
    get qeibs mqdes = Some (Valid_Addr eid, wtype, flag, maxm, msize, curm) /\ 
    get O1 curtid = Some (oscurt t) /\
    get O1 evlocid = Some (evloc locmp) /\
    get locmp t = Some (Vint32 (Int.repr __EvLoc_normal)) /\ 
    get O1 evptrid = Some (evptr ptrmp) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\
    qeibs' = set qeibs mqdes (Null, wtype, flag, maxm, msize, curm) /\ 
    locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbdel)) /\  
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
    get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbdel)) /\ 
    get O1 evptrid = Some (evptr ptrmp) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\
    locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\  
    opv = Some (Vint32 Int.zero) /\
    O_opt = Some (set O1 evlocid (evloc locmp'))
  end.

Definition mqdelete (vl: vallist) :=
  match vl with 
    v1 :: v2 :: nil =>
    mqdelete_mqdes_err (| v1 :: nil |) ?? 
    mqdelete_ecb_ptr_null (| v1 :: nil |) ??
    mqdelete_ecb_ptr_holder_abt (| v1 :: nil |) ?? 
    mqdelete_int_nst_err (| v1 :: nil |) ??
    (mqdelete_get_set_ecb_ptr (| vl |) ;;
     (qdel (v2::nil);; mqdelete_reset_loc (| v1 :: nil |)))
  | _ => ABORT
  end.

(* Local Open Scope code_scope. *)
Definition mqdeleteapi := (mqdelete, (Tint32, mqd_t :: nil)).  

(*******  qpost   *****)
Definition MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MSGQ_OVF_ERR := OS_Q_FULL.
Definition MSGQ_NULL_ERR := OS_ERR_PEVENT_NULL.

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
     exists qid msg cnt v_ret O',
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
           exists qls n ml pwl log log' cmp cnt',
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq ml n pwl, nil) /\
                 Z.lt (Z_of_nat (length ml)) (Int.unsigned n)/\ 
                 get O1 loglsid = Some (oslog log)  /\
                 log' =  log ++ ((enque qid msg cnt) :: nil) /\
                 get O1 mqcntid = Some (mqcnt cmp) /\
                 get cmp qid = Some cnt/\
                 cnt' = plus cnt 1%nat /\ 
                 O' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt (set cmp qid cnt') )/\
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ 
                  O_opt = Some ( set O' absecblsid (absecblist (set qls qid (absmsgq (ml++( (msg, cnt )::nil) ) n pwl,nil)))) \/
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
       )
  end.

Definition qpost_exwt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):= 
  match rst with
    | (opv, O_opt) =>
     exists qid msg v_ret,
       vl= (Vptr qid :: msg ::v_ret :: nil) /\
       (
         (
           exists qls wl qls' t' tls tls' m,  
           exists p st n pwl sus,
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
                 get O1 abstcblsid = Some (abstcblist tls) /\
                 get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq nil n pwl,wl) /\
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
           exists  qls (* vl *) n pwl wl ,  

               get O1 absecblsid = Some (absecblist qls) /\
               get qls qid = Some (absmsgq nil n pwl,wl) /\
               ~ wl =nil /\
               opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
               v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = None
       )
  end.

Definition qpost (vl:vallist):=
                qpost_null (|vl|)??
                qpost_msg_null (|vl|) ??
                qpost_q_type_err (|vl|) ??
                qpost_ovf_err (|vl|) ?? 
                qpost_nowt_succ  (|vl|) ??
                ( (qpost_exwt_succ (|vl|) ?? qpost_exwt_abt(|vl|)) ;; 
                  isched ;; 
                  END (Some (Vint32 (Int.repr OS_NO_ERR))) ) .

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
     exists qid time msg v_ret,
       vl =  ( (Vptr qid) :: time :: msg :: v_ret :: nil) /\
         exists tls st msg t sus,
           get O1 curtid = Some (oscurt t) /\
           get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus) /\
       opv = None/\
       O_opt = None 
  end.

Definition qtimedpost_stat_not_rdy (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret,
       vl =  ( (Vptr qid) :: time :: msg :: v_ret :: nil) /\
         exists tls st msg prio t sus,
           get O1 curtid = Some (oscurt t) /\
           get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg,sus) /\
           st <> rdy /\
       opv = None/\
       O_opt = None 
  end.

Definition qtimedpost_ovf_block(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid msg p st m time v_ret, 
       vl= (Vptr qid :: Vint32 time :: msg :: v_ret :: nil) /\
       (
           exists t qls qls' tls tls' ml n pwl wl sus,
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
             get tls t =Some (p, st, m,sus)/\
              opv = None /\
              (( ((st = rdy )  \/ ( st = wait (os_stat_postq qid) None))  /\ O_opt = Some O1)
              \/ 
              ( ~((st = rdy ) \/ ( st = wait (os_stat_postq qid) None) ) /\ O_opt = None))
         )
       )
  end.

Definition qtimedpost_timeout_err(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret  , 
       vl= (Vptr qid :: time :: msg :: v_ret ::nil) /\
       (
           exists t tls p m qls qls' ,
           exists pwl n ml wl sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t = Some (p, wait (os_stat_postq qid) None,m, sus) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get qls qid = Some (absmsgq ml n pwl, wl) /\
              In t pwl /\
              qls' = set qls qid (absmsgq ml n (remove_tid t pwl), wl)/\
              opv =  (Some (Vint32 (Int.repr OS_TIMEOUT)))/\
              ( v_ret = Vint32 (Int.repr OS_TIMEOUT) /\ 
                  O_opt = Some ( set (set O1 abstcblsid( abstcblist (set tls t (p, rdy,Vnull, sus))) ) 
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
              get tls t = Some (p,st,m, sus) /\
               st = rdy /\ 
               opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
               (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ O_opt = Some O1 \/
                v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
        )
  end. 

Definition qtimedpost_nowt_succ(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid time msg v_ret cnt,
       vl= (Vptr qid :: time :: msg ::v_ret :: nil) /\
       (
         (
           exists qls n ml pwl log log' cmp cnt' O',
              opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
              get O1 absecblsid = Some (absecblist qls) /\
              get qls qid = Some (absmsgq ml n pwl, nil) /\
              Z.lt (Z_of_nat (length ml)) (Int.unsigned n)/\
              get O1 loglsid = Some (oslog log)  /\
              log' =  log ++ ((enque qid msg cnt) :: nil) /\
              get O1 mqcntid = Some (mqcnt cmp) /\
              get cmp qid = Some cnt/\
              cnt' = plus cnt 1%nat /\ 
              O' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt (set cmp qid cnt') )/\ 
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = Some ( set O' absecblsid (absecblist (set qls qid (absmsgq (ml++( (msg, cnt )::nil) ) n pwl,nil)))) \/
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
           exists qls wl qls' t' tls tls' m,  
           exists p st n pwl sus,
            opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist qls) /\
            get qls qid = Some (absmsgq nil n pwl,wl) /\
            ~ wl =nil /\
            GetHWait tls wl t'/\
            get tls t' = Some (p,st,m, sus)/\
            tls'=set tls t' (p,rdy,msg, sus)/\
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
           exists  qls (* vl *) n pwl wl ,
               get O1 absecblsid = Some (absecblist qls) /\
               get qls qid = Some (absmsgq nil n pwl,wl) /\
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

Definition mqsend_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr 6) mqdes = true \/ mqdes =(Int.repr 6)) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.

Definition mqsend_get_msgsize  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
           opv = None /\
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
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
         opv = None /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.

Definition mqsend_ret (rv_post: val) ( rv : val) :=
      mqsend_ret_eqfull  (|rv_post :: rv :: nil|)  ??
      mqsend_ret_eqnoerr_yes (|rv_post :: rv :: nil|)  ??
      mqsend_ret_eqnoerr_no  (|rv_post :: rv :: nil|) .
 

Definition mqsend (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post  :: rv :: nil  =>
        mqsend_mqdes_err (|mqdes :: rv :: nil|) ??
        mqsend_get_msgsize (|mqdes :: rv_size :: nil|) ;;
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
                                 (  ( mqsend_mqflags_eqzero_beforepost (| rv_flag' :: nil|) ;;
                                      mqsend_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                      mqsend_set_evloc_ptr (| rv_ptr' :: nil |) ;;
                                      (qtimedpost (rv_ptr' :: Vint32 (Int.zero) :: msg_ptr :: rv_post :: nil);; 
                                        (mqsend_set_evloc_ptr (| Vnull :: nil |) ;;
                                        (mqsend_ret rv_post rv  ) ) ))
                                        ??
                                    ( mqsend_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       mqsend_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                       mqsend_set_evloc_ptr (| rv_ptr' :: nil |) ;;
                                       ((qpost (rv_ptr' :: msg_ptr :: rv_post :: nil));; 
                                        (mqsend_set_evloc_ptr (| Vnull :: nil |) ;;
                                        (mqsend_ret rv_post rv ) ) )
                                      )
                                    )
                                       ))))))
       | _ => spec_abort
  end.

(* Open Scope code_scope. *)

Definition mqsendapi := (mqsend, (Tint32, mqd_t :: Tptr char :: size_t :: unsigned ::nil) ). 

(*****  qacc********)
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
          exists log log' cnt O', 
             opv =  (Some v_ret)/\
             get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq ((msg, cnt) ::mls) n pwl,wl)/\
             get O1 loglsid = Some (oslog log) /\
             log' =  log ++ ((deque qid msg cnt) :: nil) /\
             O' = set O1 loglsid (oslog log') /\
              (v_ret = msg /\ O_opt = Some (set O' absecblsid (absecblist (set qls qid (absmsgq mls n pwl,wl))))
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
     exists tls st msg t sus,
      vl = ( nil) /\
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg, sus) /\
       (opv = None /\ O_opt = None)
  end.

Definition qpend_stat_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists tls prio st msg  t  sus,
      vl = (nil) /\
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio,st,msg, sus) /\ 
           ~ st = rdy /\
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
                 exists t qls tcbls msg ml n wl qls',
                 exists log log' cnt O', 
                  get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\                 
                  get qls qid = Some (absmsgq ((msg, cnt)::ml) n nil ,wl) /\
                  get O1 loglsid = Some (oslog log) /\
                  log' =  log ++ ((deque qid msg cnt) :: nil) /\
                  O' = set O1 loglsid (oslog log') /\
                  qls'= set qls qid (absmsgq ml n nil,wl)/\
                  opv= None/\
                  (rv = msg /\ O_opt = Some (set O' absecblsid (absecblist qls'))  
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
                 exists qls' tcbls' m t' st  sus ,
                 exists cnt cnt' cnt'' O' log log' cmp,
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\ 
                  ~ pwl = nil /\               
                  get qls qid = Some (absmsgq ((msg, cnt )::ml) n pwl ,wl) /\
                  qls'= set qls qid (absmsgq (ml++((m, cnt' )::nil)) n (remove_tid t' pwl) ,wl)/\
                  GetHWait tcbls pwl t' /\
                  get tcbls t' = Some (prio,st,m, sus)/\ 
                  tcbls' = set tcbls t' (prio,rdy,m, sus)/\
                  get O1 loglsid = Some (oslog log) /\
                  log' =  log ++ ((deque qid msg cnt ) :: (enque qid m cnt' ):: nil) /\
                  get O1 mqcntid = Some (mqcnt cmp) /\
                  get cmp qid = Some cnt' /\
                  cnt'' =  plus cnt' 1%nat /\ 
                  O' = set (set O1 loglsid (oslog log')) mqcntid (mqcnt (set cmp qid cnt'' ) )/\
                  opv= None/\
                  (rv = msg /\ O_opt = Some (set ( set O' abstcblsid (abstcblist tcbls'))
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
         exists qid v2 m,
           vl= (Vptr qid::Vint32 v2 ::nil) /\
           exists tls tls' qls qls' wl p st n t opt_t,
           exists pwl sus,
               get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                 get qls qid = Some (absmsgq nil n pwl,wl) /\
                 qls'=set qls qid (absmsgq nil n pwl,t::wl)/\
                  get O1 abtcblsid = Some (abstcblist tls) /\ 
                 get tls t = Some (p,st,m, sus) /\
                 ( v2 <> Int.zero /\ opt_t = Some v2 \/ v2 = Int.zero /\ opt_t = None ) /\
                 tls' = set tls t (p,wait (os_stat_q qid) opt_t ,m , sus) /\
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
             exists tls piro  t m els els' ml n pwl wl ,
             exists sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
              get tls t =Some (piro, wait (os_stat_q qid) (Some Int.zero), m, sus)/\
              m = Vnull /\
              get O1 absecblsid = Some (absecblist els) /\
              get els qid = Some (absmsgq ml n pwl , wl) /\
              In t wl /\
              els' = set els qid (absmsgq ml n pwl, (remove_tid t wl)) /\
              opv = None /\
            (rv = Vnull /\ O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (piro, rdy,m, sus)))) 
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
         exists tls p st m t tls' sus,
           get O1 curtid = Some (oscurt t) /\
           get O1 abtcblsid = Some (abstcblist tls)/\
           get tls t =Some (p,st,m, sus)/\
           m<>Vnull /\
           tls' = set tls t (p,rdy,Vnull, sus)/\
           opv = None /\
           (rv = m /\ O_opt = Some ( set O1 abtcblsid (abstcblist tls'))
               \/ rv <> m /\ O_opt = None)
       )
  end.

Definition qpend_set_stat (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid tls prio st msg t sus,
      vl = (Vptr qid :: nil) /\
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio,st,msg, sus) /\ 
           opv = None /\ 
           ( ((st = rdy /\ msg <> Vnull \/ st = wait (os_stat_q qid) (Some Int.zero) /\ msg = Vnull)
             /\ O_opt = Some O1) \/ 
             (~(st = rdy /\ msg <> Vnull \/ st = wait (os_stat_q qid) (Some Int.zero)  /\ msg = Vnull) 
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

Definition memcpy_empty (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists   v1 v2 v3 ,
       vl =  (v1 :: v2 :: v3 :: nil) /\
       opv = Some v1 /\ O_opt = Some O1
       
  end.

Definition memcpy_spec (vl:vallist) :=
  match vl with
      v1 :: v2 :: v3 :: nil =>
          memcpy_empty(|v1::v2::v3::nil |)
      | _ => spec_abort
  end.

Definition qreceive_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr 6) mqdes = true \/ mqdes =(Int.repr 6)) /\
           opv = Some (Vint32 (Int.mone)) /\
        (rv = (Vint32 (Int.mone)) /\ O_opt = Some O1  \/ 
         rv <> Vint32 (Int.mone) /\ O_opt = None)
  end.
  
Definition qreceive_get_msgsize  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
       opv = None /\
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
      opv = None /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.

Definition qreceive_ret (mqdes: val)(rv_flag'':val)(rv_post: val)(msg_len:val) ( rv : val) (msg_ptr:val) :=
      mqreceive_set_evloc_ptr (|Vnull :: nil|) ;;
      qreceive_get_mqflags (| mqdes :: rv_flag'' :: nil|) ;; 
      (qreceive_msg_null_flageq1_ret  (|rv_flag''::rv_post :: rv :: nil|)  ??
      qreceive_msg_null_flageq0_ret (|rv_flag'':: rv_post :: rv :: nil|)  ??
      qreceive_msg_null_ret  (|rv_flag'':: rv_post :: rv :: nil|) ??
      ((memcpy_spec (msg_ptr :: rv_post :: msg_len :: nil));;
       (qreceive_succ_ret(|msg_len::rv_post::rv::nil|)))).
  
Definition mqreceive (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: perr :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post':: rv_post  :: rv :: rv_flag'' :: nil  =>
        qreceive_mqdes_err (| mqdes :: rv :: nil|) ??
        qreceive_get_msgsize (|mqdes :: rv_size :: nil|) ;;
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
                                  ( (qreceive_mqflags_eqzero_beforepost (| rv_flag' :: nil|) ;;
                                      qreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                      mqreceive_set_evloc_ptr(|rv_ptr' :: nil|) ;; 
                                      qreceive_perr_not_null(|perr :: nil|);;
                                      ((qpendnew (rv_ptr' :: Vint32 (Int.repr 0) :: perr :: rv_post :: nil));;  
                                       (qreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                        ??
                                     (qreceive_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       qreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;;
                                       mqreceive_set_evloc_ptr (|rv_ptr' :: nil|) ;;
                                       ((qacceptnew (rv_ptr' :: rv_post :: nil));;
                                        (qreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr ))))
                                       )
                                      )))))
       | _ => spec_abort
  end.
  
Definition mqreceiveapi := (mqreceive, (ssize_t, mqd_t :: Tptr char :: size_t :: unsigned :: Tptr Int8u ::nil) ).

Definition qtimedreceive_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  rv ,
          vl= (Vint32 mqdes :: rv :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr 6) mqdes = true \/ mqdes =(Int.repr 6)) /\
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
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
          ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
           opv = None /\
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
     exists e wtype flag maxm msize curm,
          vl = ( (Vint32 mqdes) :: rv :: nil )/\
(*           ((mqdes = Int.zero \/ Int.ltu Int.zero mqdes = true) /\
             Int.ltu mqdes (Int.repr 6) = true)/\ *)
             get O1 absmqattrid = Some (absmqattr qtls)/\
             get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
             opv = None /\
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
      opv = None /\
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
         opv = None /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (Vnull, Vnull, v_pevent))))
  end.

Definition qtimedreceive_ret (mqdes: val)(rv_flag'':val)(rv_post: val)(msg_len:val) ( rv : val) (msg_ptr : val):=
      qtimedreceive_set_evloc_ptr (|Vnull :: nil|) ;;
      qtimedreceive_get_mqflags (| mqdes :: rv_flag'' :: nil|) ;; 
     (qtimedreceive_msg_null_flageq1_ret  (|rv_flag''::rv_post :: rv :: nil|)  ??
      qtimedreceive_msg_null_flageq0_ret (|rv_flag'':: rv_post :: rv :: nil|)  ??
      qtimedreceive_msg_null_ret  (|rv_flag'':: rv_post :: rv :: nil|) ??
      ((memcpy_spec (msg_ptr :: rv_post :: msg_len :: nil));;
       (qtimedreceive_succ_ret(|msg_len::rv_post::rv::nil|)))).
  
Definition mqtimedreceive (vl:vallist) :=
  match vl with
    mqdes :: msg_ptr :: msg_len :: msgprio :: abs_timeout :: perr :: rv_size :: rv_ptr :: rv_ptr' :: rv_flag :: rv_flag' :: rv_post':: rv_post  :: rv :: rv_flag'' :: nil  =>
        qtimedreceive_mqdes_err (| mqdes :: rv :: nil|) ??
        qtimedreceive_timeout_err(|abs_timeout :: rv :: nil|)??
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
                                      ((qpendnew (rv_ptr' :: abs_timeout :: perr :: rv_post :: nil));;  
                                       (qtimedreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr)))
                                        ??
                                    ( qtimedreceive_mqflags_noteqzero_beforepost (| rv_flag' :: nil|) ;;
                                       qtimedreceive_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;; qtimedreceive_set_evloc_ptr(|rv_ptr' :: nil|) ;;
                                       ((qacceptnew (rv_ptr' :: rv_post :: nil));;
                                        (qtimedreceive_ret mqdes rv_flag'' rv_post msg_len rv msg_ptr )))
                                      )))))))
       | _ => spec_abort
  end.
  
Definition mqtimedreceiveapi := (mqtimedreceive, (ssize_t, mqd_t :: Tptr char :: size_t ::Tptr unsigned :: Int16u :: Tptr Int8u ::nil) ). 


(*********qquerynew********)
Definition id_addrval (l:addrval) (id:var) (t:type) :=
  match t with
  | Tstruct s dcls => match field_offset id dcls with
                      | Some off => let (b,i):=l in
                                      Some (b, Int.add i off)
                      | None => None
                      end
  | _ => None
  end.  
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
       opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))/\
       (v_ret = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1 \/ 
        v_ret <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None)
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
             opv =  (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)))/\ 
              get O1 absecblsid = Some (absecblist qls) /\ 
             (~ exists x y pwl wls,get qls qid = Some (absmsgq x y pwl,wls) )/\ 
              (v_ret = (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = Some O1
              \/ v_ret <>  (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = None)
         ) 
     ) 
  end. 

Definition qquery_succ_if  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists qid pdata v_ret,
       vl= ((Vptr qid) :: Vptr pdata :: v_ret :: nil)/\
       (
          exists qls msg mls n pwl wl l  arrayheap l2 ,
          exists evheap evheap' evheap'' evheap''' evheap'''' ,
          exists  (qletbl : addrval) arrayheap' cnt,
             opv =  (Some (Vint32 (Int.repr OS_NO_ERR)))/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq ((msg, cnt)::mls) n pwl,wl) /\
             get O1 evstructheapid = Some (evstructheap evheap) /\
             Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) /\
             (exists i0 , evheap' = Set_struct' evheap pdata OSEventGrp (Vint32 i0)) /\ 
             (evheap'' = Set_struct' evheap' pdata OSMsg (msg))  /\
             (evheap''' = Set_struct' evheap'' pdata OSNMsgs  (Vint32 (Int.repr (Z.of_nat(length((msg, cnt)::mls))))) ) /\
             (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  /\
             
             get O1 evarrayheapid = Some (evarrayheap arrayheap) /\
             id_addrval' (Vptr pdata) log_code_defs.OSEventTbl OS_Q_DATA = Some qletbl /\
             Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) /\ 
             (exists l2', arrayheap' = Set_array' arrayheap qletbl l2') /\ 
              (v_ret = (Vint32 (Int.repr  OS_NO_ERR)) /\ O_opt = Some (set ( set O1 evarrayheapid (evarrayheap arrayheap')) evstructheapid (evstructheap evheap''''))
              \/ v_ret <>  (Vint32 (Int.repr  OS_NO_ERR)) /\ O_opt = None)
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
             opv =  (Some (Vint32 (Int.repr  OS_NO_ERR)))/\
              get O1 absecblsid = Some (absecblist qls) /\
             get qls qid =Some (absmsgq mls n pwl,wl)/\
             get O1 evstructheapid = Some (evstructheap evheap) /\
             Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l) /\
             (exists i0,evheap' = Set_struct' evheap pdata OSEventGrp  (Vint32 i0)) /\ 
             (evheap'' = Set_struct' evheap' pdata OSMsg  (Vnull))  /\
             (evheap''' = Set_struct' evheap'' pdata OSNMsgs (Vint32 (Int.repr  (Z.of_nat(length(mls))))) ) /\
             (evheap'''' = Set_struct' evheap''' pdata OSQSize  (Vint32 n))  /\
             
             get O1 evarrayheapid = Some (evarrayheap arrayheap) /\
             id_addrval' (Vptr pdata) log_code_defs.OSEventTbl OS_Q_DATA = Some qletbl /\
             Get_array arrayheap qletbl = Some (qletbl, Z.to_nat OS_EVENT_TBL_SIZE , l2) /\ 
             (exists l2', arrayheap' = Set_array' arrayheap qletbl l2') /\ 
              (v_ret = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = Some (set ( set O1 evarrayheapid (evarrayheap arrayheap')) evstructheapid (evstructheap evheap''''))
              \/ v_ret <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None)
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
  
Definition mqgetinfo_mqdes_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes  ,
          vl= (Vint32 mqdes :: nil )/\
          (Int.ltu mqdes Int.zero = true \/
          Int.ltu (Int.repr 6) mqdes = true \/ mqdes =(Int.repr 6)) /\
           opv = Some (Vint32 (Int.mone)) /\ O_opt = Some O1
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
        opv = Some  (Vint32 (Int.mone)) /\ O_opt = Some O1
  end.
  
Definition mqgetinfo_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
           get O1 absmqattrid = Some (absmqattr qtls)/\
           get qtls mqdes =Some ( e, wtype, flag, maxm, msize, curm) /\
           opv = None /\
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
        opv = Some (Vint32 (Int.mone)) /\ O_opt = Some O1
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
      opv = Some (Vint32 (Int.mone)) /\ O_opt = Some O1
  end.
  
Definition mqgetinfo_pdata_not_null 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pdata pdata',
      (vl =  pdata :: nil) /\
      opv = None /\
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
      exists (* query_rv *) mqdes evheap evheap' mq_info  vl l  ,
      exists qtls e wtype flag maxm msize curm ,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) ::  nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some ( e ,wtype ,flag ,maxm ,msize ,curm) /\ 
      evheap' = Set_struct' evheap mq_info mq_msgsize (Vint32 msize) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None 
  end.

Definition mqgetinfo_query_get_mq_waittype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) mqdes evheap evheap' mq_info vl l  ,
      exists qtls e wtype flag maxm msize curm ,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) ::  nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some ( e ,wtype ,flag ,maxm ,msize ,curm) /\ 
      evheap' = Set_struct' evheap mq_info mq_waittype (Vint32 wtype) /\  
      O_opt = Some (set O1 evstructheapid (evstructheap evheap'))  /\
      opv = None
  end.

Definition mqgetinfo_query_get_mq_flags
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists (* query_rv *) mqdes evheap evheap' mq_info vl l  ,
      exists qtls e wtype flag maxm msize curm ,
      (vl = (Vint32 mqdes) :: (Vptr mq_info) :: nil) /\
(*       Int.eq query_rv Int.zero = true /\ *)
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) /\
      get O1 absmqattrid = Some (absmqattr qtls)/\
      get qtls mqdes =Some ( e ,wtype ,flag ,maxm ,msize ,curm) /\ 
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
      evheap' = Set_struct' evheap mq_info log_code_defs.task_blocked  (Vint32 Int.zero) /\  
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
      evheap' = Set_struct' evheap mq_info log_code_defs.task_blocked (Vint32 (Int_add_n vblocked vh Int.one)) /\  
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
      rv_for_ptr :: rv_tid_ptr1 :: rv_tid_ptr2 :: rv_tcbevent_ptr :: oseventtbl_addr1::oseventtbl_addr2 ::nil  =>
        mqgetinfo_mqdes_err (|mqdes :: nil|)??
        mqgetinfo_mq_info_err (| mq_info :: nil|) ??
        mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr :: nil|) ;;
        (
            mqgetinfo_if_null_yes (| rv_ptr :: nil|) ??
            mqgetinfo_if_null_no (| rv_ptr :: nil|) ;;
            mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr' :: nil|) ;; 
            mqgetinfo_pdata_not_null(|pdata :: nil|);;
            (
              (qquerynew (rv_ptr' :: pdata :: query_rv :: nil)) ;; 
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
                                       mqgetinfo_query_get_task_blocked(| mq_info ::nil|);; 
                                       mqgetinfo_get_ecb_ptr (|mqdes :: rv_ptr''''' :: nil|) ;;
                                       ( mqgetinfo_if_null_yes (| rv_ptr''''' :: nil|) ??
                                         mqgetinfo_if_null_no (| rv_ptr''''' :: nil|) ;;
                                              (mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                                (mqgetinfo_query_after_while_set_blocked(|rv_ptr''''' :: mq_info ::nil|) ;;
                                                  ( mqgetinfo_mq_info_validptr_err(|mq_info :: nil|)??
                                                   mqgetinfo_pdata_validptr_err(|pdata :: nil|)??
                                                   mqgetinfo_query_memcpy_get_mq_info_oseventtbl(|mq_info ::oseventtbl_addr1::nil |);;
                                                    mqgetinfo_query_memcpy_get_pdata_oseventtbl(|pdata ::oseventtbl_addr2::nil |);;
                                                    ((memcpy_spec (oseventtbl_addr1 :: oseventtbl_addr2 :: (Vint32 (Int.repr OS_EVENT_TBL_SIZE)) :: nil));;
                                                     (mqgetinfo_succ_ret(|nil|)))
                                              )))
                                          ) 
                                       )
                                  )     
                             )
                        )
                     )
                  )
              )
            )
        )
   | _ => spec_abort
  end.
  
Definition mqgetinfoapi := (mqgetinfo, (Tint32, mqd_t :: Tptr mq_info_t :: Tptr OS_Q_DATA ::nil) ). 



