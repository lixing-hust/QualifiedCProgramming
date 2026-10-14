
Require Import memory. 
Require Import if_language.
Require Import if_opsem.

Section UserSpace. 
  Parameter userAddrStart : addrval. 
  Parameter userAddrEnd : addrval.  
End UserSpace. 

Parameter vhold_addr : addrval.

Definition OS_NO_ERR := 0%Z.
Definition OS_ERR_EVENT_TYPE := 1%Z.
Definition OS_ERR_POST_NULL_PTR :=3%Z.
Definition OS_ERR_PEVENT_NULL := 4%Z.

Definition OS_TIMEOUT := 10%Z.

Definition OS_Q_FULL := 30%Z.
Definition MSG_NULL_ERR := OS_ERR_POST_NULL_PTR.
Definition MSGQ_OVF_ERR := OS_Q_FULL.
Definition MSGQ_NULL_ERR := OS_ERR_PEVENT_NULL.

Definition O_NONBLOCK := 1%Z.

Definition OS_LOWEST_PRIO := 63%Z.
Definition OS_IDLE_PRIO := OS_LOWEST_PRIO. 

Parameter DNUM : Z.
Parameter dnum_range :  Z.le 0 DNUM /\  Z.le DNUM 7.

Definition OS_PARTITION_MESSAGE_COME := 1%Z.

Definition PORT_NUMS := 64%Z.
Definition OS_PORT_ID_INVALID := 162%Z.
Definition OS_PORT_ERR_NULL := 164%Z.
Definition OS_PORT_ERR_TYPE := 165%Z.
Definition OS_ERR_PORT_NO_CHANNEL := 169%Z.
Definition OS_CHANNEL_ERR_BEING_USED := 178%Z.
Definition OS_PORT_ERR_DIRECTION_TYPE := 184%Z.
Definition OS_ERR_PARTITION_UNMAPPED := 190%Z.

Definition CAP_PORT_CLASS := 10%Z. 
Definition PORT_POST_CAP := 64%Z.
Definition PORT_PEND_CAP := 4%Z. 
Definition PORT_ACCEPT_CAP := 1%Z. 

Definition CAP_CATEGORY_TYPE : Z := 1.
Definition CAP_OBJECT_TYPE : Z := 2.  
Definition CAP_QUEUE_CLASS : Z := 5.

Definition Q_PEND_CAP : Z := 2.
Definition Q_ACCEPT_CAP : Z := 4.  
Definition Q_POST_CAP : Z := 8.

Definition USER_CAPABILITY_NONE : Z := 252. 

Definition OBJ_POSITION := 17%Z. (* 0x11 *) 

Parameter OS_EVENT : type. 

(* notation for the annotation of assertions on program statements *)  
Notation " 'SCHED' " := (sched trivial_asrt) (at level 40). 
Notation "asrt '#' x '[|' vl '|]' " := (spec_prim asrt vl x) (at level 40). 
Notation "asrt '#' 'ASSUME' b" := (spec_assume asrt b) (at level 40). 
Notation "asrt '#' 'ASSERT' b" := (spec_assert asrt b) (at level 40). 
Notation "'Aif' '|' asrt '|' ( E ) { S1 } 'else' { S2 }" := (spec_ifelse asrt E S1 S2) (at level 45, right associativity).  
Notation "'AIF' '|' asrt '|' ( E ) { S1 } 'ELSE' { S2 }" := (spec_if_else_ asrt E S1 S2) (at level 45, right associativity).

(* Definition GetHWaitD (tls: TcbMod.map) (wl: list tid) (t: tid) := *)
(*   In t wl /\  *)
(*     exists p st msg sus pr td, *)
(*       get tls t = Some (p, st, msg, sus, pr) /\ dom_for_prio pr = Some td *)
(*       /\ forall t', t <> t' -> In t' wl ->  *)        

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.

Definition GetHWait (tls: TcbMod.map) (wl: list tid) (t: tid) := 
  In t wl /\ 
    exists p st msg sus p0,
      get tls t = Some (p,st,msg,sus,p0)/\
        forall t',
          t<>t' ->
          In t' wl -> 
          exists p' st' msg' sus' p0',
            get tls t' = Some (p',st',msg',sus',p0') /\ (Int.ltu p0 p0' = true)%Z. 


Local Open Scope int_scope. 


(* (* there is a task in the partition td, with the capability PORT_POST_CAP *) *)
(* Definition has_post_cap (tls: tid->option priority) cspc td :=  *)
(*   exists t p0,  *)
(*   exists vls vlp slot_tp cap_tp content cc cr objp,      *)
(*     tls t = Some p0 /\ *)
(*     dom_for_prio p0 = td /\ *)
(*     get cspc p0 = Some (vls, vlp) /\ (* vls is the val list holding instances of slot_t *) *)
(*     List.nth_error vls (Z.to_nat CAP_PORT_CLASS) = Some (slot_tp, (cap_tp, content)) /\ *)
(*     content = (cc, cr, objp) /\  *)
(*     Int.eq (cr &ᵢ ($PORT_POST_CAP)) Int.zero = false.  *)


(* (* Corresponds to struct cap_t. *)

(*    If type = CAP_CATEGORY_TYPE, then the first two fields are *)
(*    category_content and category_right. If type = CAP_OBJECT_TYPE, *)
(*    then the first field is object_right and third field is objec_t. *)
(* *) *)
(* Definition ACap (l: addrval) (v: int32 * cap_content_type) := *)
(*     match v with  *)
(*     | (cap_type, (x, y, z)) => *)
(*     let (b, i) := l in  *)
(*         PV l @ Tint32 |-> (Vint32 cap_type) ** *)
(*         PV (b, i +ᵢ $ 4) @ Tint32 |-> Vint32 x ** *)
(*         PV (b, i +ᵢ $ 8) @ Tint32 |-> Vint32 y **  *)
(*         PV (b, i +ᵢ $ 12) @ Tptr Tvoid |-> z ** *)
(*         [|isptr z|] *)
(*     end.  *)

Definition has_cat_cap (pr: priority) cspc (cls: Z) (cap: Z) :=  
  exists vls vlp cap_tp content cc cr objp,
    get cspc pr = Some (vls, vlp) /\ (* vls is the val list holding instances of slot_t *) 
      List.nth_error vls (Z.to_nat cls) = Some ($CAP_CATEGORY_TYPE, (cap_tp, content)) /\
      content = (cc, cr, objp) /\ 
      Int.eq (cr &ᵢ ($cap)) Int.zero = false.

Definition has_obj_cap (pr: priority) cspc (objptr: val) := 
  exists vls vlp i cap_tp content cc cr, 
    get cspc pr = Some (vls, vlp) /\
      OBJ_POSITION <= Z_of_nat i /\
      List.nth_error vls i = Some ($CAP_OBJECT_TYPE, (cap_tp, content)) /\ 
      content = (cc, cr, objptr) /\ 
      cc <> Int.zero. 

(* there is a task in the partition td, with the capability PORT_POST_CAP *)
Definition has_post_cap (tls: tid->option priority) cspc td :=
  exists t p0,
    tls t = Some p0 /\
      dom_for_prio p0 = td /\
      has_cat_cap p0 cspc CAP_PORT_CLASS PORT_POST_CAP.
   
Definition tps_tst_corr (O: osabst) (tps: tid->option priority) := 
  exists tls,
    get O abstcblsid = Some (abstcblist tls)
    /\ (forall t st p p0 msg sus,
           get tls t = Some (p, st, msg, sus, p0) ->
           ((* st = rdy /\ *) tps t = Some p0))
    /\ (forall t p0,
           tps t = Some p0 ->
           exists p st msg sus, get tls t = Some (p, st, msg, sus, p0)).


Parameter mqidx_in_dom: int32 -> taskdom -> bool.

Definition mq_ptr (O: osabst) (idx: int32) (ptr: val) :=
  exists mqs eo wtp qflg mmsg msz cmsgs sltidxs,  
    get O absmqattrid = Some (absmqattr mqs)
    /\ get mqs idx = Some (eo, wtp, qflg, mmsg, msz, cmsgs, sltidxs)
    /\ (eo = Null /\ ptr = Vnull \/ exists p, eo = Valid_Addr p /\ ptr = Vptr p). 

Definition dom_cur_tsk (O: osabst) (td: taskdom) :=
  exists t pr,
    get O curtid = Some (oscurt t)
    /\ task_prio_id O pr t
    /\ dom_for_prio pr = td.


Definition ret_val (vl: vallist) (O: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v1, 
      vl = v1::nil 
      /\ opv = Some v1 
      /\ act = TauAct
      /\ O_opt = Some O
  end.


(* "buf_in_dom eid td" represents that eid identifies a buffer that is domain td *) 
Parameter buf_in_dom: addrval -> taskdom -> bool.
