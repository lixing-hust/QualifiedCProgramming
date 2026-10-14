Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.
Require Import os_inv.

(* FIXME: Semaphore pend
 should be implemented by other group *)
Parameter OSIPCSemPend_spec : ecbid -> nat -> spec_code.

(* Parameter OSIPCSemPend_spec : ident (* name of semaphore array *) -> coreid (* coreid of the semaphore *) -> nat -> spec_code. *)

(**************************** ipcrecv *********************************)

Definition ipc_list :=
  CORE0_IPC :: CORE1_IPC :: CORE2_IPC :: CORE3_IPC :: CORE4_IPC :: CORE5_IPC :: CORE6_IPC :: CORE7_IPC :: nil.

Definition IPCINFO_brach (n:nat) (mask:Z) :=
  (Int.or (Int.repr (nth n ipc_list CORE0_IPC)) (Int.repr mask)).

Definition ipcrecv_err_invalid (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O2) =>
    (
    exists srcCore dstAddr size rflag,
      vl = ((Vint32 srcCore) :: dstAddr :: (Vint32 size) :: (Vint32 rflag) :: nil) /\
      ( dstAddr = Vnull \/ 
        (Int.ltu size (Int.repr 1) = true) \/ (Int.ltu (Int.repr IPC_STEP) size = true) \/
        (Int.ltu (Int.sub (Int.repr CORENUM) Int.one) srcCore = true) \/
        (Int.eq srcCore (Int.repr DNUM) = true) \/ 
        (Int.ltu (Int.repr IPC_BROAD) rflag = true)) /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O2 = Some O1
    )
  end.

Definition In_heapl_addrval (cheapl : list (addrval * nat * (list val))) (l: addrval) (n: nat) := exists m vl, In (l, m, vl) cheapl /\ n <= m.

Definition Get_heapl_addrval (cheapl : list (addrval * nat * (list val))) (l: addrval) (n: nat) (res: vallist) :=
  exists m vl, In (l, m, vl) cheapl /\ n <= m /\
    res = (firstn n vl).

Definition update_heapl_addrval (cheapl : list (addrval * nat * (list val))) (l: addrval) (n: nat) (vl: list val) (resh : list (addrval * nat * (list val))) : Prop :=
    exists cheapl1 m vl1 vl2 cheapl2, cheapl = cheapl1 ++ (l,m,vl1 ++ vl2)::cheapl2 /\
    length vl1 = n /\ length vl = n /\  resh = cheapl1 ++ (l,m,vl ++ vl2)::cheapl2.

Fixpoint set_nth {A: Type} (n: nat) (l: list A) (v: A) : option (list A) :=
  match l with
  | nil => None
  | v' :: l => match n with
               | O => Some (v :: l)
               | S n => match set_nth n l v with
                        | None => None
                        | Some l' => Some (v' :: l')
                        end
               end
  end.

Definition compute_step (srcCore: nat) (dnum : nat) : nat :=
  if dnum <? srcCore then (srcCore - 1) else srcCore.

Definition ipcrecv_valid_vl (vl : vallist) (O : osabst) := 
  match vl with
  | (Vint32 srcCore) :: (Vptr dstAddr) :: (Vint32 size) :: (Vint32 rflag) :: nil 
       =>  ( 
       (Int.ltu size (Int.repr 1) = false) /\ (Int.ltu (Int.repr IPC_STEP) size = false) /\
       (Int.ltu (Int.sub (Int.repr CORENUM) Int.one) srcCore = false) /\
       (Int.eq srcCore (Int.repr DNUM) = false) /\ 
       (Int.ltu (Int.repr IPC_BROAD) rflag = false)) 
  | _ => False
  end.

Definition ipcrecv_before_pend' (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists v' sid t ptrmp ptrmp',
        vl = (v' :: nil) /\
        opv = None /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (Vnull, Vnull, Vnull) /\
        ptrmp' = set ptrmp t (Vnull, Vptr sid, Vnull) /\
        (v' = Vptr sid /\ O_opt = Some (set O1 evptrid (evptr ptrmp'))
          \/ v' <> Vptr sid /\ O_opt = None )
  end. 

Definition ipcrecv_before_pend_IPCSem v : spec_code :=
  match v with 
  | Vint32 dstCore =>
      match nth_error OSIPCSem_val (Z.to_nat (Int.unsigned dstCore)) with
      | Some e => ipcrecv_before_pend' (| (Vptr e) :: nil|)
      | None => spec_abort
      end
  | _ => spec_abort
  end.

Definition ipcrecv_before_pend_IPCSemShared : spec_code :=
  ipcrecv_before_pend' (| (Vptr OSSemShared_val) :: nil|).

Definition ipcrecv_after_pend 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists t ptrmp ptrmp',
      vl = nil /\ opv = None /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        O_opt = Some (set O1 evptrid (evptr ptrmp'))
  end.

Definition sempend_ipcsem v k : spec_code :=
  match v with
  | Vint32 srcCore =>
      match nth_error OSIPCSem_val (Z.to_nat (Int.unsigned srcCore)) with
      (* | Some e => OSIPCSemPend_spec e 0 *)
      | Some e => sem_pend ((Vptr e) :: (Vint32 Int.zero) :: k :: nil)
      | None => spec_abort
      end
  | _ => spec_abort
  end.
 
Definition ipcrecv_memcpy (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O2) =>
     opv = None /\
     exists srcCore dstAddr size rflag v dnum ,
      vl = ((Vint32 srcCore) :: (Vptr dstAddr) :: (Vint32 size) :: (Vint32 rflag) :: v :: nil) /\
      get O1 curcoreid = Some (oscurtcore dnum) /\ 
     exists recvheap cHeapl cHeape cHeapt, 
         get O1 ipcrecvid = Some (osrecv recvheap) /\
         get O1 oscoreheapid = Some (oscoreheap (cHeapl,cHeape, cHeapt)) /\
         ((In_heapl_addrval cHeapl dstAddr (Z.to_nat (Int.unsigned size)) /\
          ((*non broad *) Int.eq rflag (Int.repr IPC_BROAD) = false /\
          exists step vl cHeapl', step = compute_step (Z.to_nat (Int.unsigned srcCore)) dnum /\
          nth_error recvheap step = Some vl /\
          update_heapl_addrval cHeapl dstAddr (Z.to_nat (Int.unsigned size)) (firstn (Z.to_nat (Int.unsigned size)) vl) cHeapl' /\
          O2 = Some (set O1 oscoreheapid (oscoreheap (cHeapl', cHeape, cHeapt)))) \/ 
          ((*broad *)Int.eq rflag (Int.repr IPC_BROAD) = true /\ 
          exists srccore, v = Vint32 srccore /\
          exists step vl cHeapl',step = compute_step (Z.to_nat (Int.unsigned srccore)) dnum /\
          nth_error recvheap step = Some vl /\
          update_heapl_addrval cHeapl dstAddr (Z.to_nat (Int.unsigned size)) (firstn (Z.to_nat (Int.unsigned size)) vl) cHeapl' /\
          O2 = Some (set O1 oscoreheapid (oscoreheap (cHeapl', cHeape, cHeapt))))
          ) \/
          (~ In_heapl_addrval cHeapl dstAddr (Z.to_nat (Int.unsigned size)) /\ O2 = None)
          )
  end.


Definition IPCINFO_case (dnum : nat) : int32 :=
      if Nat.eqb dnum O then (Int.or (Int.repr CORE0_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 1%nat then (Int.or (Int.repr CORE1_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 2%nat then (Int.or (Int.repr CORE2_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 3%nat then (Int.or (Int.repr CORE3_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 4%nat then (Int.or (Int.repr CORE4_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 5%nat then (Int.or (Int.repr CORE5_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 6%nat then (Int.or (Int.repr CORE6_IPC) (Int.repr IPC_MESSAGE_ACK))
  else if Nat.eqb dnum 7%nat then (Int.or (Int.repr CORE7_IPC) (Int.repr IPC_MESSAGE_ACK))
  else  (Int.or (Int.repr CORE0_IPC) (Int.repr IPC_MESSAGE_ACK)).

Definition ipcrecv_nonack (v: val) : absexpr :=
 fun (O : osabst ) => match v with 
  | Vint32 rflag => Int.eq rflag (Int.repr IPC_NONACK) = true
  | _ => False 
  end.

Definition ipcrecv_succ_ack vl : spec_code :=
  match vl with 
  | Vint32 srcCore' :: _ :: _ :: Vint32 rflag :: v :: _ => 
    if (Int.eq rflag (Int.repr IPC_BROAD)) then 
    match v with 
    | Vint32 srccore => 
    let srcCore := (Z.to_nat (Int.unsigned srccore)) in 
      ( coreint srcCore (Vint32 (IPCINFO_case 0%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 1%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 2%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 3%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 4%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 5%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 6%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 7%nat)))
    | _ => spec_abort end 
      else 
    let srcCore := (Z.to_nat (Int.unsigned srcCore')) in 
      ( coreint srcCore (Vint32 (IPCINFO_case 0%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 1%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 2%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 3%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 4%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 5%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 6%nat)) ??
        coreint srcCore (Vint32 (IPCINFO_case 7%nat)))
  | _ => spec_abort
end.

(*ipcrecv broad : *)
Definition sempend_ipcsemshared k : spec_code :=
  sem_pend ((Vptr OSSemShared_val) :: (Vint32 Int.zero) :: k :: nil).
  
Definition ipcrecv_nonbroad v3 (O : osabst) :=
  match v3 with  
  | Vint32 rflag  => Int.eq rflag (Int.repr IPC_BROAD) = false 
  | _ => False 
  end.

Definition ipcrecv_broad_error (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with 
  | (opv,O2) =>
     opv = (Some (Vint32 (Int.repr EBUSY))) /\ 
     exists srcCore dstAddr size rflag v,
      vl = ((Vint32 srcCore) :: (Vptr dstAddr) :: (Vint32 size) :: (Vint32 rflag) :: 
      v :: nil) /\ 
      Int.eq rflag (Int.repr IPC_BROAD) = true /\ 
      ( get O1 ipcbroadid = Some (osipcbroad error_broad_stack) \/
        get O1 ipcbroadid = Some (osipcbroad nil)) /\ 
      O2 = Some O1
  end.

Definition ipcrecv_middelval (v:val) (O : osabst) : Prop :=
  match v with 
  | Vint32 rstsrccore => exists broadstack broadstack',  
        get O ipcbroadid = Some (osipcbroad broadstack) /\ 
        broadstack = (Z.to_nat (Int.unsigned rstsrccore)) :: broadstack'
  | _ =>  False
  end.

Definition ipcrecv_broad (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with 
  | (opv,O2) =>
     opv = None /\ 
     exists srcCore dstAddr size rflag rstsrccore broadstack,
      vl = ((Vint32 srcCore) :: (Vptr dstAddr) :: (Vint32 size) :: (Vint32 rflag) :: 
      (Vint32 rstsrccore) :: nil) /\ 
      Int.eq rflag (Int.repr IPC_BROAD) = true /\ 
      get O1 ipcbroadid = Some (osipcbroad broadstack) /\ 
      exists broadstack', broadstack = (Z.to_nat (Int.unsigned rstsrccore)) :: broadstack' /\
      O2  = Some (set O1 ipcbroadid (osipcbroad broadstack'))
  end.
 
(* v4 is a logic val : is the middle rst core *)
Definition ipcrecvcode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 :: v1 :: v2 :: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: v4 :: vl'  => 
                    ipcrecv_err_invalid (|(v0::v1::v2::v3::nil)|)??
                    (
                      ASSUME (ipcrecv_valid_vl (v0::v1::v2::v3::nil)) ;;
                      (
                        ( (* non broad case : sem pend *)
                          ipcrecv_before_pend_IPCSem v0;;
                          spec_code_cons (sempend_ipcsem v0 (Vint32 (Int.repr OS_NO_ERR)))
                          (ipcrecv_after_pend (|nil|) ;;
                          ipcrecv_memcpy (|(v0::v1::v2::v3::v4::nil)|) ;; 
                          (* ack or nonack *)
                          (ASSUME (ipcrecv_nonack v3) ?? 
                          ipcrecv_succ_ack (v0::v1::v2::v3::v4::nil) ) ;;
                          (* return value *)
                          END (Some (Vint32 (Int.repr OS_NO_ERR))))
                        ) ??
                        ( 
                          (*broad case : sem pend *)
                          ipcrecv_before_pend_IPCSemShared;;
                          spec_code_cons (sempend_ipcsemshared (Vint32 (Int.repr OS_NO_ERR)))
                          (ipcrecv_after_pend (|nil|) ;;
                          ( ipcrecv_broad_error (|(v0::v1::v2::v3::v4::nil)|) ??
                          ASSERT (ipcrecv_middelval v4) ;;
                          ipcrecv_broad (|(v0::v1::v2::v3::v4::nil)|);;
                          (* memcpy *)
                          ipcrecv_memcpy (|(v0::v1::v2::v3::v4::nil)|) ;; 
                          (* ack or nonack *)
                          (ASSUME (ipcrecv_nonack v3) ?? 
                          ipcrecv_succ_ack (v0::v1::v2::v3::v4::nil) ) ;;
                          (* return value *)
                          END (Some v4)))
                        )
                      )
                  ) 
  end.

Definition ipcrecvapi := (ipcrecvcode, (Tint16, Tint8 :: (Tptr Tvoid) :: Tint32 :: Tint8 :: Tint32 ::nil)).



(* IPCsend *)

Definition set_sendheap (n: nat) (sh: list vallist) (size: nat) (v: vallist) (sh': list vallist) :=
  exists l1 l2 w, sh = l1 ++ w :: l2 /\
    length l1 = n /\ sh' = l1 ++ (v ++ (skipn size w)) :: l2.

Definition ipcsend_err_invalid (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    exists dstCore srcAddr size flag,
      vl = ((Vint32 dstCore) :: srcAddr :: (Vint32 size) :: (Vint32 flag) :: nil) /\
      (
        srcAddr = Vnull \/
        Int.ltu size (Int.repr 1) = true \/
        Int.ltu (Int.repr IPC_STEP) size = true \/
        Int.ltu (Int.sub (Int.repr CORENUM) (Int.repr 1)) dstCore = true \/
        Int.eq dstCore (Int.repr DNUM) = true \/
        Int.ltu (Int.repr IPC_BROAD) flag = true 
      ) /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O2 = Some O1
  end.

Definition ipcsend_memcpy_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    opv = None /\
    exists dstCore srcAddr size flag,
      vl = ((Vint32 dstCore) :: (Vptr srcAddr) :: (Vint32 size) :: (Vint32 flag) :: nil) /\
      (* get O1 curcoreid = Some (oscurtcore dnum) /\ *)
      (* (
        Int.ltu Int.zero size = false \/
        Int.ltu (Int.repr IPC_STEP) size = true \/
        (* (Int.ltu (Int.sub (Int.repr CORENUM) Int.one) srcCore = true) \/ *)
        Int.ltu dstCore (Int.repr CORENUM) = false \/
        Int.eq dstCore (Int.repr (Z.of_nat dnum)) = true \/
        Int.ltu flag (Int.repr IPC_BROAD) = false
      ) /\ *)
      exists sendheap cHeapl cHeape cHeapt,
        get O1 ipcsendid = Some (ossend sendheap) /\
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
        In_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) /\
        exists sendh_idx vl sendheap',
          Get_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) vl /\
         (* ((Int.unsigned dstCore > DNUM)%Z /\ stepz = DNUM \/
         (Int.unsigned dstCore < DNUM)%Z /\ stepz = (DNUM - 1)%Z) /\ *)
         sendh_idx = (Z.to_nat (Int.unsigned dstCore)) - (if Z.to_nat DNUM <? (Z.to_nat (Int.unsigned dstCore)) then 1 else 0) /\
          set_sendheap sendh_idx sendheap (Z.to_nat (Int.unsigned size)) vl sendheap' /\
          O2 = Some (set O1 ipcsendid (ossend  sendheap'))
  end.

Definition ipcsend_memcpy_err (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    opv = None /\
    exists dstCore srcAddr size flag,
      vl = ((Vint32 dstCore) :: (Vptr srcAddr) :: (Vint32 size) :: (Vint32 flag) :: nil) /\
      exists cHeapl cHeape cHeapt,
      get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      ~ In_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) /\ O2 = None
  end.

Definition ipcsend_memcpy (vl: vallist) : spec_code :=
  ipcsend_memcpy_succ (|vl|) ?? ipcsend_memcpy_err (|vl|).

Definition ipcsend_getsem v : spec_code :=
  match v with
  | Vint32 dstCore => getsem (Z.to_nat (Int.unsigned dstCore))
  | _ => spec_abort
  end.

Definition ipcsend_postsem v : spec_code :=
  match v with
  | Vint32 dstCore => postsem (Z.to_nat (Int.unsigned dstCore))
  | _ => spec_abort
  end.

Definition ipcsend_before_pend' (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists v' sid t ptrmp ptrmp',
        vl = (v' :: nil) /\
        opv = None /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (Vnull, Vnull, Vnull) /\
        ptrmp' = set ptrmp t (Vnull, Vptr sid, Vnull) /\
        (v' = Vptr sid /\ O_opt = Some (set O1 evptrid (evptr ptrmp'))
          \/ v' <> Vptr sid /\ O_opt = None )
  end. 

Definition ipcsend_before_pend v : spec_code :=
  match v with 
  | Vint32 dstCore =>
      match nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore)) with
      | Some e => ipcsend_before_pend' (| (Vptr e) :: nil|)
      | None => spec_abort
      end
  | _ => spec_abort
  end.

Definition ipcsend_sendsempend_if v (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    exists flag, v = Vint32 flag /\
      (flag = Int.repr IPC_BLOCK /\ O2 = Some O1) \/
      (flag <> Int.repr IPC_BLOCK /\ O2 = None)
  end. 

Definition ipcsend_sendsempend_else v (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    exists flag, v = Vint32 flag /\
      (flag = Int.repr IPC_BLOCK /\ O2 = None) \/
      (flag <> Int.repr IPC_BLOCK /\ O2 = Some O1)
  end. 

Definition ipcsend_sendsempend v k : spec_code :=
  match v with
  | Vint32 dstCore =>
      match nth_error OSSendSem_val (Z.to_nat (Int.unsigned dstCore)) with
      | Some e => sem_pend ((Vptr e) :: (Vint32 Int.zero) :: k :: nil)
      | None => spec_abort
      end
  | _ => spec_abort
  end.

Definition ipcsend_after_pend 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists t ptrmp ptrmp',
      vl = nil /\ opv = None /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\ 
        O_opt = Some (set O1 evptrid (evptr ptrmp'))
  end.

Definition ipcsend_generateipc_if dnum (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    (get O1 curcoreid = Some (oscurtcore dnum) /\
      O2 = Some O1) \/
    (get O1 curcoreid <> Some (oscurtcore dnum) /\
      O2 = None)
  end.

Definition ipcsend_generateipc_else (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    exists dnum, get O1 curcoreid = Some (oscurtcore dnum) /\
    ((dnum < 0 \/ dnum > 7) /\
      opv = None /\ O2 = Some O1) \/
    (0 <= dnum /\ dnum <= 7 /\
      O2 = None)
  end.



Definition ipcsend_generateipc_rdy v :=
  match v with
  | Vint32 dstCore' => let dstCore := (Z.to_nat (Int.unsigned dstCore')) in 
      (coreint dstCore (Vint32 (IPCINFO_brach 0 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 1 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 2 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 3 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 4 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 5 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 6 IPC_MESSAGE_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 7 IPC_MESSAGE_RDY)))
      (* (ipcsend_generateipc_if 0 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 0 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 1 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 1 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 2 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 2 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 3 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 3 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 4 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 4 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 5 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 5 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 6 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 6 IPC_MESSAGE_RDY))) ??
      (ipcsend_generateipc_if 7 (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 7 IPC_MESSAGE_RDY))) ??
      (* seems this branch is not required *)
      (ipcsend_generateipc_else (|nil|) ;; coreint dstCore (Vint32 (IPCINFO_brach 0 IPC_MESSAGE_RDY))) *)
  | _ => spec_abort
  end.

Definition ipcsend_generateipc_broad v :=
  match v with
  | Vint32 dstCore' => let dstCore := (Z.to_nat (Int.unsigned dstCore')) in 
      (coreint dstCore (Vint32 (IPCINFO_brach 0 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 1 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 2 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 3 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 4 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 5 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 6 IPC_MESSAGE_BROAD))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 7 IPC_MESSAGE_BROAD)))
  | _ => spec_abort
  end.

Definition ipcsendcode (vl: vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 :: v1 :: v2 :: nil => spec_abort
  | v0 (* dstcore *) :: v1 (* srcaddr *) :: v2 (* size *) :: v3 (* flag *) :: vl' => 
      ipcsend_err_invalid (|(v0::v1::v2::v3::nil)|) ??
      (
        ipcsend_getsem v0 ;;
        ipcsend_memcpy (v0::v1::v2::v3::nil) ;;
        ( ipcsend_generateipc_broad v0 ??
          ipcsend_generateipc_rdy v0) ;; 
        ( (ipcsend_before_pend v0 ;; 
          spec_code_cons  (ipcsend_sendsempend v0 (Vint32 (Int.repr OS_NO_ERR)))
          (ipcsend_after_pend (|nil|)  ;;
          ipcsend_postsem v0 ;;
          END (Some (Vint32 (Int.repr OS_NO_ERR)))) )?? 
        (END None ;;
          ipcsend_postsem v0 ;;
          END (Some (Vint32 (Int.repr OS_NO_ERR)))))
      )
  end.

Definition ipcsendapi := (ipcsendcode, (Tint16, Tint8 :: (Tptr Tvoid) :: Tint32 :: Tint8 :: nil)).

(**************************** dynamic refactor *********************************)

Definition refactsend_err_invalid (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    exists dstCore srcAddr size,
      vl = ((Vint32 dstCore) :: srcAddr :: (Vint32 size) :: nil) /\
      (
        srcAddr = Vnull \/
        Int.ltu size (Int.repr 1) = true \/
        Int.ltu (Int.repr IPC_STEP) size = true \/
        Int.ltu (Int.sub (Int.repr CORENUM) (Int.repr 1)) dstCore = true \/
        Int.eq dstCore (Int.repr DNUM) = true 
      ) /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O2 = Some O1
  end.

(* Definition set_sendheap2 (n: nat) (sh: list vallist) (v: vallist) (sh': list vallist) :=
  exists l1 l2 w, sh = l1 ++ w :: l2 /\
    length l1 = n /\ sh' = l1 ++v :: l2. *)

Definition refactsend_memcpy_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
    opv = None /\
    exists dstCore srcAddr size,
      vl = ((Vint32 dstCore) :: (Vptr srcAddr) :: (Vint32 size) :: nil) /\
      exists sendheap cHeapl cHeape cHeapt,
        get O1 ipcsendid = Some (ossend sendheap) /\
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
        In_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) /\
        exists sendh_idx vl sendheap',
          Get_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) vl /\
         sendh_idx = (Z.to_nat (Int.unsigned dstCore)) - (if Z.to_nat DNUM <? (Z.to_nat (Int.unsigned dstCore)) then 1 else 0) /\
          set_sendheap sendh_idx sendheap (Z.to_nat (Int.unsigned size)) vl sendheap' /\
          O2 = Some (set O1 ipcsendid (ossend  sendheap'))
  end.

Definition refactsend_memcpy_err (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
  opv = None /\
  exists dstCore srcAddr size,
    vl = ((Vint32 dstCore) :: (Vptr srcAddr) :: (Vint32 size) :: nil) /\
    exists cHeapl cHeape cHeapt,
    get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
    ~ In_heapl_addrval cHeapl srcAddr (Z.to_nat (Int.unsigned size)) /\ O2 = None
end.

Definition refactsend_memcpy (vl: vallist) : spec_code :=
  refactsend_memcpy_succ (|vl|) ?? refactsend_memcpy_err (|vl|).
  
Definition refactsend_generateipc_refactor_rdy v :=
  match v with
  | Vint32 dstCore' => let dstCore := (Z.to_nat (Int.unsigned dstCore')) in 
      (coreint dstCore (Vint32 (IPCINFO_brach 0 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 1 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 2 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 3 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 4 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 5 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 6 REFACTOR_RDY))) ??
      (coreint dstCore (Vint32 (IPCINFO_brach 7 REFACTOR_RDY)))
  | _ => spec_abort
  end.
  
  Definition refactsendcode (vl: vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 (* dstcore *) :: v1 (* srcaddr *) :: v2 (* size *) :: vl' => 
      refactsend_err_invalid (|(v0::v1::v2::nil)|) ??
      (
        (*ASSERT (fun O => exists sendheap, get O ipcsendid = Some (ossend  sendheap));;*)
        refactsend_memcpy (v0::v1::v2::nil) ;;
        refactsend_generateipc_refactor_rdy v0 ;;
        END (Some (Vint32 (Int.repr OS_NO_ERR)))
      )
  end.
  
Definition refactsendapi := (refactsendcode, (Tint16, Tint8 :: (Tptr Tvoid) :: Tint32 :: nil)).

Fixpoint del_n {A:Type} (n:nat)(l:list A):=
  match n with
  | O => l
  | 1 => l
  | 2 => match l with
               | nil => nil
               | v::vl => vl
               end
  | S n' => match l with
              | nil => nil
              | v:: vl => del_n n' vl
              end
  end.

Definition del_prio_list:=
 map Int.repr (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::
 18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::
 38::39::40::41::42::43::44::45::46::47::48::49::50::51::52::53::54::55::56::
 57::58::59::60::nil)%Z.

Fixpoint taskclear (k: spec_code) (prio: list int32):spec_code:=
                  match prio with
                  | nil =>   k
                  | v::vl =>  ( spec_code_cons (taskdelcode (Vint32 v:: nil))  
                                      ( END (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) ?? 
                                       END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ??
                                       END (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) ??
                                        END (Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER))) ??
                                        END (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) ??
                                        taskclear k  vl ) )
                                       ?? (taskclear k  vl) 
                   end.

Definition dynamic_refactor_pend_taskclear(k: spec_code):= taskclear k del_prio_list.

(* Definition dynamic_refactor_qpend_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
     (
         exists timeout  err_addr,
           vl= (Vptr dynrefcmsgQ_addr:: Vint32 timeout:: Vptr err_addr::nil) /\
           (
             (
               exists qls n qls' tcbls tcbls',
                 exists msg ml prio m wl t,
                  get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\
                 get qls dynrefcmsgQ_addr = Some (absmsgq (msg::ml) n,wl) /\
                 get tcbls t = Some (prio,rdy ,m)/\
                 qls'=set qls dynrefcmsgQ_addr (absmsgq ml n,wl)/\
                 tcbls' = set tcbls t (prio,rdy ,msg) /\
                 O2= Some ( set ( set O1 abstcblsid (abstcblist tcbls'))
                                    absecblsid (absecblist qls')) /\
                 opv= (Some msg)
             ) 
           
       )
     )
  end.  *)
  
(*   Definition dynamic_refactor_qpend_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
     (
         exists timeout  p,
           vl= (Vptr dynrefcmsgQ_addr:: Vint32 timeout:: Vptr p::nil) /\
           (
             (
               exists qls n qls' tcbls tcbls',
                 exists ml prio m wl t,
                  get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\
                 get qls dynrefcmsgQ_addr = Some (absmsgq (Vptr p::ml) n,wl) /\
                 get tcbls t = Some (prio,rdy ,m)/\
                 qls'=set qls dynrefcmsgQ_addr (absmsgq ml n,wl)/\
                 tcbls' = set tcbls t (prio,rdy , Vptr p) /\
                 O2= Some ( set ( set O1 abstcblsid (abstcblist tcbls'))
                                    absecblsid (absecblist qls')) /\
                 opv= (Some (Vptr p))
             ) 
           
       )
     )
  end.  *)



(* Definition dynamic_refactor_pend_taskcre (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
         match rst with (opv, O2) =>
           vl = nil /\
           (exists cHeapl cHeape cHeapt cfgp cfgvl,
            exists elfp prionew ehdrvl entryp stackp, 
            get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
            Get_heapt_addrval cHeapt cfgp dyn_refac_cfg cfgvl /\
            V_dyn_refac_cfg_elf cfgvl = Some (Vptr elfp) /\
            V_dyn_refac_cfg_prio cfgvl = Some (Vint32 prionew) /\
            Get_heapt_addrval cHeapt elfp Elf32_Ehdr ehdrvl /\
            V_e_entry ehdrvl = Some (Vptr entryp) /\
            taskcre_succ (Vptr entryp:: stackp:: Vint32 prionew::nil) O1 rst 
            )
        end . *)

(* Definition dynamic_refactor_pend_code (vl:vallist): spec_code:=
  match vl with
  | nil => spec_abort
  | v:: vl' =>  qpend (Vptr dynrefcmsgQ_addr::vl) ;; (END (Some (Vint32 (Int.mone))) ??  dynamic_refactor_pend_taskclear ((ASSERT (fun O:osabst => exists cHeapl cHeape cHeapt cfgp cfgvl,
            exists elfp prionew ehdrvl entryp,  
            get O oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
            Get_heapt_addrval cHeapt cfgp dyn_refac_cfg cfgvl /\
            V_dyn_refac_cfg_elf cfgvl = Some (Vptr elfp) /\
            V_dyn_refac_cfg_prio cfgvl = Some (Vint32 prionew) /\
            Get_heapt_addrval cHeapt elfp Elf32_Ehdr ehdrvl /\
            V_e_entry ehdrvl = Some (Vptr entryp)
              ) ) ;; dynamic_refactor_pend_taskcre (|nil|)) 
)
  end. *)

Definition In_heapt_addrval (cheapt : list (addrval * type * (list val))) (l: addrval) (t:type):= exists  vl, In (l,t,  vl) cheapt. 

Definition Get_heapt_addrval (cheapt : list (addrval * type * (list val))) (l: addrval) (t:type) (res: vallist) :=
  exists tp vl, In (l, tp, vl) cheapt /\  t = tp /\ res = vl.

Definition update_heapt_addrval (cheapt : list (addrval * type * (list val))) (l: addrval) (vl: list val) (resh : list (addrval * type * (list val))) : Prop :=
    exists cheapt1 tp vl1 cheapt2, cheapt = cheapt1 ++ (l, tp, vl1)::cheapt2 /\  struct_type_vallist_match tp vl /\ resh = cheapt1 ++ (l, tp, vl)::cheapt2.
    
Definition dynheap_add (heap: list (addrval * (list val))) (l:addrval)(vl:list val): list (addrval * (list val)):=
  (l,vl)::heap.

Fixpoint Coreheapt_remove (p:addrval)(l: list (addrval * type * list val) ):=
  match l with
  | nil => nil
  | (p0,t,v)::l' => if addrval_eq_dec p p0 then Coreheapt_remove p l' else (p0,t,v):: Coreheapt_remove p l'
  end.
  
 Fixpoint set_Coreheapt (p:addrval)(vl: vallist)(l: list (addrval * type * list val) ):=
  match l with
  | nil => nil
  | (p0,t,v)::l' => if addrval_eq_dec p p0 then (p0,t,vl)::set_Coreheapt p vl l' else (p0,t,v):: set_Coreheapt p vl l'
  end.
  
  Definition dynamic_refactor_pend_reomove_coreheapt (vl : vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with (opv, O2) =>
           exists cfgp,
           vl= (Vptr cfgp::nil) /\
             (
               exists cHeapl cHeape cHeapt,
                 get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
                 O2= Some ( set  O1 oscoreheapid (oscoreheap (cHeapl, cHeape, Coreheapt_remove cfgp cHeapt))) /\
                 opv= None
             ) 
  end.   
  
Definition dynamic_refactor_pend_code (vl:vallist): spec_code:=
  match vl with
  | v1 (*timeout *):: (Vptr v2) (* cfgp *):: (Vptr v3) (*elfp *)::(Vptr v4) (* entryp*) :: v5 (* prio *) :: v6 (*err*)::nil =>  
         spec_code_cons (qpendnew ((Vptr dynrefcmsgQ_addr:: v1:: v6::nil) ++ (Vptr v2::nil))) (END (Some (Vint32 (Int.mone))) ??  
         dynamic_refactor_pend_taskclear ((ASSERT (fun O:osabst => exists cHeapl cHeape cHeapt,
            get O oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
             In_heapt_addrval cHeapt v2 dyn_refac_cfg /\
             ( exists cfgvl, Get_heapt_addrval cHeapt v2 dyn_refac_cfg cfgvl /\ 
               V_dyn_refac_cfg_elf cfgvl = Some (Vptr v3) /\
               V_dyn_refac_cfg_prio cfgvl = Some v5 /\ 
               In_heapt_addrval (Coreheapt_remove v2  cHeapt) v3 Elf32_Ehdr /\
               ( exists ehdrvl,
                Get_heapt_addrval (Coreheapt_remove v2  cHeapt)  v3 Elf32_Ehdr ehdrvl /\
                V_e_entry ehdrvl = Some (Vptr v4))
                ) ))  ;; dynamic_refactor_pend_reomove_coreheapt (|Vptr v2::nil|);; taskcrecode ((Vptr v4):: Vnull:: Vnull:: v5::nil);;  (END (Some (Vint32 (Int.zero))) 
                ?? END (Some (Vint32 (Int.mone)))) ))
 | _ => spec_abort
   end.
  
Definition dynamic_refactor_pend_api := (dynamic_refactor_pend_code, (Tint32, Tint16 :: nil)).