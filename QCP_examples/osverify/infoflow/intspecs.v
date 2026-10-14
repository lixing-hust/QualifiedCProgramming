Require Import memory.
Require Import if_language.
Require Import if_opsem.

(* Definition OS_NO_ERR := 0%Z. *)

(* notation for the annotation of assertions on program statements *)  
Notation " 'SCHED' " := (sched trivial_asrt) (at level 40). 
(* Notation "asrt '#' x '[|' vl '|]' " := (spec_prim asrt vl x) (at level 40).  *)
(* Notation "asrt '#' 'ASSUME' b" := (spec_assume asrt b) (at level 40).  *)
(* Notation "asrt '#' 'ASSERT' b" := (spec_assert asrt b) (at level 40).  *)
(* Notation "'Aif' '|' asrt '|' ( E ) { S1 } 'else' { S2 }" := (spec_ifelse asrt E S1 S2) (at level 45, right associativity).   *)
(* Notation "'AIF' '|' asrt '|' ( E ) { S1 } 'ELSE' { S2 }" := (spec_if_else_ asrt E S1 S2) (at level 45, right associativity). *)

Notation abtcblsid:=abstcblsid.

(* Definition in_rtbl (st:taskstatus):=
  match st with
    | rdy => True
    | wait x t_opt => match t_opt with
                                     | Some time => if Int.eq time Int.zero then True else False
                                     | None => False
                                  end
  end. *)

(* Definition get_hprio_d (O:osabst) (t:tid) : Prop :=  
  exists tls prio st msg pr d,
    get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, st, msg, false, pr) /\ 
      in_rtbl st /\ 
      get O kscurdomid = Some (kscurdom d) /\ 
      dom_for_prio pr = d /\ 
      forall i prio' st' msg' pr',
        i <> t ->
        get tls i = Some (prio', st', msg', false, pr') -> 
        in_rtbl st' ->
        dom_for_prio pr' = d -> 
        Int.ltu prio prio' = true.
 *)

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
                 (msg0 : msg) (sus0 : susstatus) pr tls_used tls_used',
                 TcbMod.joinsig t (p, st, msg0, sus0, pr) tls_used' tls_used ->
                 tickchange t st els st' els' ->
                 set tls t (p, st', msg0, sus0, pr) = tls' ->
                 tickstep' tls' els' tls'' els'' tls_used'->
                 tickstep' tls els tls'' els'' tls_used.

Definition tickstep tls els tls' els' := tickstep' tls els tls' els' tls.

Definition tickisr_spec (vl: vallist) (O : osabst) (act: action) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
      exists tls els tm,
      exists tls' els' tm',
      exists dt dt' O' O'',
        act = TauAct /\
          get O abstcblsid = Some (abstcblist tls) /\
          get O absecblsid = Some (absecblist els)/\
          get O ostmid = Some (ostm tm) /\
          tm'=(Int.add tm Int.one)/\
          tickstep tls els tls' els'/\
          get O ksdomtimeid = Some (ksdomtime dt) /\
          dt' = Int.sub dt Int.one /\
          O'=
            ( set ( set ( set O absecblsid (absecblist els')) abstcblsid (abstcblist tls'))
                ostmid (ostm tm')) /\
          O'' = (set O' ksdomtimeid (ksdomtime dt')) /\
          ((Int.eq dt' Int.zero = true /\
              exists idx len cd ld kscd idx' ld',
              exists dom kscd_len cd' dt',
              exists O1 O2 O3 O4,
                get O ksdschedidxid = Some (ksdschedidx idx) /\
                  get O ksdschedlenid = Some (ksdschedlen len) /\
                  get O kscurdomid = Some (kscurdom cd) /\
                  get O kslastdomid = Some (kslastdom ld) /\
                  get O ksdschedid = Some (ksdsched kscd) /\
                  idx' = (if (Int.ltu (Int.add idx Int.one) len) then (Int.add idx Int.one) else Int.zero) /\
                  ld' = cd /\
                  KsDScdMod.get kscd idx' = Some (dom, kscd_len) /\
                  cd' = dom /\
                  dt' = kscd_len /\
                  O1 = set O'' ksdschedidxid (ksdschedidx idx') /\
                  O2 = set O1 kslastdomid (kslastdom ld') /\
                  O3 = set O2 kscurdomid (kscurdom cd') /\
                  O4 = set O3 ksdomtimeid (ksdomtime dt') /\
                  O_opt = Some O4)
           \/
             ( Int.eq dt' Int.zero = false /\ O_opt = Some O'')) /\
          opv = None
  end.

(* Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc). *)
(* Definition tickisr :=
  tickisr_spec (|nil|);; (isched ;; END None ?? END None). *)

(* Definition spec_skip_step_isr *)
(*   (vl: vallist) (O: osabst) (act: action) (res: option val * option osabst) :=  *)
(*   let (vopt, Oopt) := res in (vopt = None /\ Oopt = Some O /\ act = SchAct). *)

(* Definition spec_skip_isr := spec_skip_step_isr (|nil|). *)

Definition tickisr :=
  tickisr_spec (|nil|);; SCHED ;; spec_skip_step (|nil|).

(* Definition OSTickISR := 5%nat.

Definition int_spec_list := (OSTickISR, tickisr) :: nil.

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.

Definition int_spec  := convert_int_spec int_spec_list. *)

