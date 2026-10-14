
Require Import memory.
Require Import if_language.
Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.


Definition OSTCBHighRdy:= 59%Z.
Definition OSTCBCur:=60%Z.

(* Definition gets_g (s:osstate):= (fst (fst (fst (fst s)))). *)
(* Definition gets_m (s:osstate) := (snd (fst (fst s))). *)
Definition get_env (m:smem):= (snd (fst m)).

Definition Dteq (D1 D2:clientst)(t:tid):Prop:=
  match D1 with 
    | ( _ ,evs1, _) => match D2 with
                         | ( _, evs2, _) =>
                           forall (t':tid), ~(t'=t) ->  get evs1 t' = get evs2 t'
                       end
  end. 

(* Definition Piteq (pi1 pi2: ltaskstset) (t:tid):Prop:= *)
(*   forall (t':tid), ~(t'=t) -> get pi1 t'= get pi2 t'. *)

(* Definition Steq (S1 S2 :osstate) (t:tid):Prop:= *)
(*   match S1 with *)
(*     | (D1, ir,  pi1)  => match S2 with  *)
(*                            | ( D2 , ir',  pi2) => Dteq D1 D2 t /\ Piteq pi1 pi2 t *)
(*                          end *)
(*   end. *)

Definition Dnewt (D:clientst) (t:tid):clientst:=
  match D with 
    | ( ge, cvs,  M) => ( ge, ( set cvs t emp), M)
  end.

(* Definition Tlnewt (tl:ltaskstset) (t:tid) :ltaskstset:= *)
(*   set tl t (true, nil, nil). *)

(* Definition Snewt (S:osstate) (t:tid):osstate:= *)
(*   match S with *)
(*     | (D, ir, tl) =>  ((Dnewt D t),   ir,  (Tlnewt tl t)) *)
(*   end. *)


Definition projD (D:clientst) (t:tid) := 
  match D with (x,y,z) => 
               match  get y t with
                 | Some e => Some (x, e , z)
                 | _ => None
               end
  end.

(* Definition projS (S:osstate) (t:tid) := *)
(*   match S with ( x, y, z)  => *)
(*                match (projD x t),(get z t) with *)
(*                  | Some m,Some n => Some (m , y  , n) *)
(*                  | _,_ => None *)
(*                end *)
(*   end. *)


Definition vtoZ (v:val):option Z:=
  match v with
    | Vint32 a => Some (Int.unsigned a)
    |_=>None
  end.


(* modified by zhanghui*)
Open Scope Z_scope.
Definition type_val_match (t:type) (v:val) :=
  match t,v with
    | Tnull, Vnull => true
    | Tptr t, Vnull => true
    | Tcom_ptr id,Vnull => true
    | Tint8,Vint32 v => (*if v is in the range of Tint8 return True, if not return False*)
      match (Int.unsigned v) <=? Byte.max_unsigned with
        | true => true
        | false => false
      end
    | Tint16,Vint32 v => (*if v is in the range of Tint16 return True, if not return False*)
      match (Int.unsigned v) <=? Int16.max_unsigned with
        | true => true
        | false => false
      end
    | Tint32,Vint32 v =>true
    | Tptr t,Vptr l => true
    | Tcom_ptr id,Vptr l => true
    | Tarray _ _, _ => true
    | Tstruct _ _, _ =>true
    | _,_=> false
  end.

Fixpoint tl_vl_match (tl:typelist) (vl:vallist) :=
  match tl with 
    | nil => 
      match vl with 
        | nil => true
        | _ => false
      end
    | t :: tl' => 
      match vl with
        | v :: vl' => if type_val_match t v then tl_vl_match tl' vl' else false
        | _ => false
      end
  end.  

Fixpoint field_offsetfld (id:var) (fld:decllist) (pos:int32):option int32:=
  match fld with 
    |dnil => None
    |dcons id' t fld'=>if Zeq_bool id id' then Some pos else field_offsetfld id fld' (Int.add (Int.repr (Z_of_nat (typelen t))) pos)
  end.

Definition field_offset (id:var) (fld:decllist) : option int32:= field_offsetfld id fld (Int.zero).

Definition istrue (v:val) : option bool :=
  match v with 
    | Vptr a => Some true
    | Vnull => Some false
    | Vint32 a =>  if (Int.eq a Int.zero) then Some false else Some true
    | _ => None
  end.

Fixpoint revlcons (d1 d2 :decllist): decllist :=
  match d1 with 
    | dnil => d2 
    | dcons x y d1' => revlcons d1' (dcons x y d2)
  end.

Fixpoint callcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> None
    | kcall  f  y z ks'=> Some (kcall f  y z ks')
    | kseq x  ks' => callcont ks'
    | kassignl x y ks' => callcont ks'
    | kassignr x y ks' => callcont ks'
    (*
| kcalle x y z ks' => callcont ks'
     *)
    | kfuneval  x y z w ks' => callcont ks'
    | kif x y ks' => callcont ks'
    | kwhile x y ks' => callcont ks'
    | kret  ks' => callcont ks'
    | kevent _ _ ks' => callcont ks'
  end .

Fixpoint intcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> Some (kint x y e ks')
    | kcall f  y z ks'=> None
    | kseq x  ks' => intcont ks'
    | kassignl x y ks' => intcont ks'
    | kassignr x y ks' => intcont ks'
    (*
| kcalle x y z ks' => intcont ks'
     *)
    | kfuneval   x y z w ks' => intcont ks'
    | kif x y ks' => intcont ks'
    | kwhile x y ks' => intcont ks'
    | kret  ks' => intcont ks'
    | kevent _ _ ks' => intcont ks'
  end .

Fixpoint absintcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> absintcont ks'
    | kcall f  y z ks'=> absintcont ks'
    | kseq x  ks' => absintcont ks'
    | kassignl x y ks' => absintcont ks'
    | kassignr x y ks' => absintcont ks' 
    | kfuneval   x y z w ks' => absintcont ks'
    | kif x y ks' => absintcont ks'
    | kwhile x y ks' => absintcont ks'
    | kret  ks' => absintcont ks'
    | kevent c ke ks' => Some (kevent c ke ks')
  end .


Fixpoint AddStmtToKs (s:stmts) (ks:stmtcont):stmtcont:=
  match ks with
    | kstop => kseq s kstop
    | kseq s' ks' => kseq s' (AddStmtToKs s ks')
    | kcall f x E ks' => kcall f x  E (AddStmtToKs s ks')
    | kint c ke e ks' => kint c ke e (AddStmtToKs s ks')
    | kassignl e t ks' => kassignl e t (AddStmtToKs s ks')
    | kassignr v t ks' => kassignr v t (AddStmtToKs s ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddStmtToKs s ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddStmtToKs s ks')
    | kif s' s'' ks' => kif s' s'' (AddStmtToKs s ks')
    | kwhile e s' ks' => kwhile e s' (AddStmtToKs s ks')
    | kret ks' => kret (AddStmtToKs s ks')

    | kevent a b  ks' => kevent a b (AddStmtToKs s ks')
  end.


Fixpoint AddKsToTail (ks1 ks2:stmtcont):stmtcont:=
  match ks2 with
    | kstop => ks1
    | kseq s' ks' => kseq s' (AddKsToTail ks1 ks')
    | kcall f x E ks' => kcall f x E (AddKsToTail ks1 ks')
    | kint c ke e ks' => kint c ke e (AddKsToTail ks1 ks')
    | kassignl e t ks' => kassignl e t (AddKsToTail ks1 ks')
    | kassignr v t ks' => kassignr v t (AddKsToTail ks1 ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddKsToTail ks1 ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddKsToTail ks1 ks')
    | kif s' s'' ks' => kif s' s'' (AddKsToTail ks1 ks')
    | kwhile e s' ks' => kwhile e s' (AddKsToTail ks1 ks')
    | kret  ks' => kret  (AddKsToTail ks1 ks')
    | kevent a b  ks' => kevent a b (AddKsToTail ks1 ks')
  end.


Notation " ks2 '##' ks1 " := (AddKsToTail ks1 ks2)(at level 25, left associativity).

Fixpoint len_exprcont (ke : exprcont) : nat :=
  match ke with
    | kenil => O
    | keop1 _ _ ke' => S (len_exprcont ke')
    | keop2r _ _ _ _ ke' => S (len_exprcont ke')
    | keop2l _ _ _ _ ke' => S (len_exprcont ke')
    | kederef _ ke' => S (len_exprcont ke')
    | keoffset _ ke' => S (len_exprcont ke')
    | kearrbase _ _ ke' => S (len_exprcont ke')
    | kearrindex _ _ ke' => S (len_exprcont ke')
    | kecast _ _ ke' => S (len_exprcont ke')
  end.

Fixpoint len_stmtcont (ks : stmtcont) : nat :=
  match ks with
    | kstop => O
    | kseq _ ks' => S (len_stmtcont ks')
    | kcall  _ _ _ ks' => S (len_stmtcont ks')
    | kint _ _ _ ks' => S (len_stmtcont ks')
    | kassignl _ _ ks' => S (len_stmtcont ks')
    | kassignr _ _ ks' => S (len_stmtcont ks')
    (*
  | kcalle _ _ _ ks' => S (len_stmtcont ks')
     *)
    | kfuneval  _ _ _ _ ks' => S (len_stmtcont ks')
    | kif _ _ ks' => S (len_stmtcont ks')
    | kwhile _ _ ks' => S (len_stmtcont ks')
    | kret ks' => S (len_stmtcont ks')

                    
    | kevent a b ks' => S (len_stmtcont ks')
  end.


Definition nilcont (s:stmts): code := ((curs s), (kenil, kstop)).

Definition is_int_type t:=
  match t with
    | Tint8 => true
    | Tint16 => true
    | Tint32 => true
    | _ => false
  end.

Fixpoint evaltype (e:expr) (m:smem){struct e}:option type:=
  match m with 
      (genv, lenv, _) =>
      match e with
      | enull => Some Tnull
      | econst32 n => Some Tint32
      | eptrconst a => Some (Tptr Tint32)
      | evar x => match get lenv x with 
                      | Some (pair a t) =>  Some t 
                      | None => match get genv x with 
                                  | Some (pair a t) => Some t 
                                  | None => None
                                end
                    end
        | eunop uop e1 => match evaltype e1 m with
                            | Some t => uop_type t uop 
                            | None => None
                          end
        | ebinop bop e1 e2 => match evaltype e1 m, evaltype e2 m  with
                                | Some t1, Some t2 => bop_type t1 t2 bop
                                | _, _ => None
                              end   
        | ederef e' => match evaltype e' m with
                         | Some (Tptr t) => Some t
                         (*if type is Tcom_ptr ??*)
                         | _ => None
                       end
        | eaddrof e' => match e' with
                          | evar x  =>  match evaltype e' m  with
                                          | Some t =>  Some (Tptr t)
                                          | None => None
                                        end
                          | ederef e'' =>  match evaltype e'' m with
                                             | Some (Tptr t) => Some (Tptr t)
                                             | _=> None
                                           end
                          | efield e'' id  =>  match evaltype e' m  with
                                                 | Some t =>  Some (Tptr t)
                                                 | None => None
                                               end
                          | earrayelem e1 e2 =>  match evaltype e' m  with
                                                   | Some t =>  Some (Tptr t)
                                                   | None => None
                                                 end
                          | _ => None
                        end
        | efield e' id => match evaltype e' m with
                            | Some (Tstruct id' dl) => ftype id dl
                            | _=> None
                          end
        | ecast e' t => match evaltype e' m, t with 
                        | Some (Tptr t'), Tptr t'' => Some t
                        | Some Tnull, Tptr t' => Some t
                        | Some (Tcom_ptr t'), Tptr t'' => Some t  
                        (* conversion from ptr to int not supported by the current mem model? *)
                        (* | Some (Tptr t'), Tint32 => Some t *)
                        (* | Some Tnull, Tint32 => Some t *)
                        (* | Some (Tcom_ptr t'), Tint32 => Some t  *)
                        | Some Tint8 , Tint8 => Some t
                        | Some Tint8 , Tint16 => Some t
                        | Some Tint8 , Tint32 => Some t
                        | Some Tint16 , Tint8 => Some t
                        | Some Tint16 , Tint16 => Some t
                        | Some Tint16 , Tint32 => Some t
                        | Some Tint32 , Tint8 => Some t
                        | Some Tint32 , Tint16 => Some t
                        | Some Tint32 , Tint32 => Some t
                        | _,_ => None
                        end

        | earrayelem e1 e2 => match evaltype e1 m, evaltype e2 m with
                                |Some (Tarray t n), Some Tint8 => Some t
                                |Some (Tarray t n), Some Tint16 => Some t
                                |Some (Tarray t n), Some Tint32 => Some t
                                |Some (Tptr t), Some Tint8 => Some t
                                |Some (Tptr t), Some Tint16 => Some t
                                |Some (Tptr t), Some Tint32 => Some t
                                | _ , _=>None
                              end
      end
  end.

Inductive assign_type_match : type -> type -> Prop:=
| eq_tnull: forall t1, (exists t, t1 = (Tptr t)) \/ (exists t,t1=(Tcom_ptr t)) \/ (t1=Tnull) -> assign_type_match t1 Tnull 
| eq_tvoid: assign_type_match Tvoid Tvoid
| eq_vptr: forall t1 t2, (exists t t', t1= (Tptr t) /\ t2 = (Tptr t'))->
                         assign_type_match t1 t2
| eq_vcomptr: forall t1 t2, ((exists t, t1= (Tptr t)) \/ (exists t, t1= (Tcom_ptr t))) /\ ((exists id,t2 = (Tcom_ptr id))\/(exists t,t2 = Tptr t)) ->
                            assign_type_match t1 t2
| eq_array: forall t1 t2, (exists t n, t1= (Tarray t n) /\ t2 = (Tarray t n))->
                          assign_type_match t1 t2
| array_to_vptr:  forall t1 t2, (exists t n, t1= (Tptr t) /\ t2 = (Tarray t n))->
                                assign_type_match t1 t2
| eq_struct: forall t1 t2,  (exists id dl, t1= (Tstruct id dl) /\ t2 = (Tstruct id dl))->
                            assign_type_match t1 t2
| eq_int: forall t1 t2, ((t1=Tint8\/t1=Tint16\/t1=Tint32)/\(t2=Tint8\/t2=Tint16\/t2=Tint32))->
                        assign_type_match t1 t2.



Fixpoint typematch (el:exprlist) (dl:decllist) (m:smem) :Prop:=
  match el,dl with
    | nil,dnil => True
    | cons e el',dcons x t dl' => (exists t',evaltype e m = Some t' /\ assign_type_match t t')/\ typematch el' dl' m
    | _,_=> False
  end.

Definition getoff (b:block) (i:offset) (id:ident) (e:expr) (m:smem):option addrval:=
  match evaltype e m with
    | Some (Tstruct id' dl) => match field_offset id dl with
                                 | Some off => Some ( b, ( Int.add (Int.repr i) off))
                                 | _ => None
                               end
    | _ => None
  end.


Definition get_genv (m : smem) :=
  match m with
    | (ge, le , M) => ge
  end.


Definition get_lenv (m : smem) :=
  match m with
    | (ge, le , M) => le
  end.


Definition get_mem (m : smem) :=
  match m with
    | (ge, le , M) => M
  end.

Definition addrval_to_addr (a:addrval):=
  match a with
    | (b,i) => (b,Int.unsigned i)
  end.
Definition addr_to_addrval (a:addr):=
  match a with
    | (b,i) => (b,Int.repr i)
  end.


Parameter addr_in_dom: addr -> taskdom -> bool.

Definition addrval_in_dom (a: addrval) (d: taskdom) : bool :=
  match a with
    (b, i) => addr_in_dom (b, (Int.intval i)) d
  end.

(* Parameter mqidx_in_dom: int32 -> taskdom -> bool. *)

Definition addr0: addr := ((xI xH)%positive, 0%Z).

(* Check (addr_in_dom addr0 Dom3 = true). *)

(* the memory for domain d maps any address in any domain d'<>d to None *) 
Definition get_dom_mem (m: mem) (d: taskdom) : mem :=
  (fun a =>  if addr_in_dom a d then (get m a) else None).

Definition task_prio_id (O: osabst) (pr: priority) (t: tid) :=
  exists pr' tcbs st msg sus,
    get O abstcblsid = Some (abstcblist tcbs) /\ get tcbs t = Some (pr', st, msg, sus, pr).

Definition dom_for_prio (pr: priority) : taskdom := Int.shr pr (Int.repr (3%Z)). 

(* assume no block goes across the boundary between two domains *) 
Definition load_pt
  (t : type) (m : mem) (l : addr) (d: taskdom) :
  option val :=  
  if addr_in_dom l d then 
    (match t with 
     | Tarray _ _ => Some (Vptr (addr_to_addrval l)) 
     | _ => loadm t m l 
     end)
  else None.  

Definition cast_eval i t t':=
  match t,t' with
    | Tint8,Tint8 => Some i
    | Tint8,Tint16 => Some i
    | Tint8,Tint32 => Some i
    | Tint16,Tint16 => Some i
    | Tint16,Tint32 => Some i
    | Tint32,Tint32 => Some i
                            
    | Tint32,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | Tint32,Tint16 => Some  (Int.modu i (Int.repr Int16.modulus))
    | Tint16,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | _,_ => None
  end.


Lemma cast_eval_tptr_none:
  forall x t,cast_eval x (Tptr t) (Tptr t) = None.
Proof.
  intros.
  simpl.
  auto.
Qed.


Fixpoint evalval (e:expr) (m:smem) (d: taskdom) : option val:= 
  match evaltype e m with
    | Some t =>  
        match e with 
        | enull => Some Vnull
        | econst32 n => Some (Vint32 n)
        | eptrconst a => Some (Vptr a)
        | evar x => match get (get_lenv m) x with
                      | Some (pair a t) => load_pt t (get_mem m) (a,0%Z) d
                      | None =>
                        match get (get_genv  m) x with
                          | Some (pair a t) => load_pt t (get_mem m) (a,0%Z) d
                          | None => None
                        end
                    end
        | eunop op1 e' =>  match evalval e' m d with
                             | Some v=> uop_eval v op1
                             | _ => None
                           end
                             
        | ebinop op2 e1 e2 =>  match evalval e1 m d, evalval e2 m d with
                                 | Some v1,Some v2 => match evaltype e1 m, evaltype e2 m with
                                                        | Some t1, Some t2 => bop_eval v1 v2 t1 t2 op2
                                                        | _,_ => None
                                                      end 
                                 | _,_ => None
                               end
        | eaddrof e' =>  match e' with
                           | evar x =>  evaladdr e' m d
                           | ederef e'' => evalval e'' m d
                           | efield e'' id => evaladdr e' m d
                           | earrayelem e1 e2 => evaladdr e' m d
                           | _ => None
                         end
        | ederef e' => match evalval e' m d with
                         | Some (Vptr ad) =>  load_pt t (get_mem  m) (addrval_to_addr ad) d
                         | _ => None
                       end
        | efield e' id => match (evaladdr e' m d) with
                            | (Some (Vptr ( b,  i))) => match getoff b (Int.unsigned i) id e' m with
                                                          | Some ad => load_pt t (get_mem m) (addrval_to_addr ad) d
                                                          | _ => None
                                                        end
                            | _ => None
                          end
        | ecast e' t' =>
          match evaltype e' m with
            | Some te =>
              match is_int_type te,is_int_type t' with
                | true, true =>
                  match evalval e' m d with
                    | Some (Vint32 x) => match (cast_eval x te t') with
                                           | Some x' => Some (Vint32 x')
                                           | None => None
                                         end
                    | _ => None
                  end
                | _ , _ => evalval e' m d
              end
            | _ => None
          end
        | earrayelem e1 e2 => match (evalval e1 m d),(evalval e2 m d) with
                                |Some (Vptr ( b,  i)), Some v =>
                                 match v with
                                   | Vint32 z => load_pt t (get_mem m) ( b, Int.unsigned (Int.add i
                                                                                               (Int.mul (Int.repr (Z_of_nat (typelen t))) z ))) d
                                   |_ => None
                                 end
                                |_,_=>None
                              end
                                
      end
    | _ => None
  end
with evaladdr (e:expr) (m:smem) (d: taskdom) :option val:=
       match e with
         | evar x => match get (get_lenv m) x with
                       |Some (pair a t) => Some (Vptr (a,Int.zero))
                       |_ => match get (get_genv m) x with
                               |Some (pair a t) => Some (Vptr (a,Int.zero))
                               |_ => None
                             end
                     end
         | ederef e' => evalval e' m d
         | efield e' id => match evaladdr e' m d with
                             | (Some (Vptr ( b, i))) => match getoff b (Int.unsigned i) id e' m with
                                                          |Some ad => Some (Vptr  ad)
                                                          |_=> None
                                                        end
                             | _ => None
                           end
         | earrayelem e1 e2 => match (evaltype e1 m), (evalval e1 m d),(evalval e2 m d) with
                                 |Some (Tarray t n), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |Some (Tptr t), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |_, _ ,_=>None
                               end
         |_=> None
       end.


Fixpoint getaddrlist (l:list (prod var (prod block type))):list (prod block type):=
  match l with
    | nil => nil
    | cons (pair x (pair ad t)) l'=> cons (pair ad t) (getaddrlist l')  
  end.

Definition getaddr (le:env):list (prod block type):=
  match le with
    | EnvMod.listset_con a _=> getaddrlist a
  end.

Fixpoint tlmatch (tl:typelist) (dl:decllist) :Prop:=
  match tl with
    | nil => match dl with
               | dnil => True
               | _ => False
             end
    | cons t tl' => match dl with
                      | dcons  _ t' dl'=> tlmatch tl' dl'/\ t'=t
                      | _ => False
                    end
  end.


Inductive estep:
  taskdom -> cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop :=
| enull_step :
  forall m ke d,
    estep d (cure enull) ke m [Vnull] ke m 
| ec32_step:
  forall (i:int32) (m:smem) (ke:exprcont) d, 
    estep d (cure (econst32 i)) ke m [Vint32 i] ke m
| eptrc_step:
  forall a m ke d, 
    estep d (cure (eptrconst a)) ke m [Vptr a] ke m
| evar_step :
  forall (x:var) (v:val) (m:smem) (ke:exprcont) d,
    evalval (evar x) m d = Some v ->  estep d (cure (evar x)) ke m [v] ke m
| eaddr_step:
  forall (x:var) (v:val) (m:smem) (ke:exprcont) d,
    evalval (eaddrof (evar x)) m d = Some v ->  
    estep d (cure (eaddrof (evar x))) ke m [v] ke m
| ederef_step:
  forall (e:expr) (t:type) (m:smem) (ke:exprcont) d,
    evaltype e m = Some (Tptr t) -> 
    estep d (cure (ederef e)) ke m (cure e) (kederef t ke) m
| eaddrderef_step:
  forall e m ke d,
    estep d (cure (eaddrof (ederef e))) ke m (cure e) ke m
| esidaddr_step:
  forall (e:expr) (id id':ident) i (dl:decllist) (ke:exprcont) (m:smem) d,
    evaltype e m = Some (Tstruct id' dl) ->
    field_offset id dl = Some i -> 
    estep d (cure (eaddrof (efield e id))) ke m (cure (eaddrof e))
      (keoffset i ke) m
| eaptrelemaddr_step:
  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem) d,
    evaltype e1 m = Some (Tptr t) ->  
    estep d (cure (eaddrof (earrayelem e1 e2))) ke m  
      (cure e1) (kearrbase e2 t ke) m
| eaelemaddr_step:
  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem) d,
    evaltype e1 m = Some (Tarray t n) ->  
    estep d (cure (eaddrof (earrayelem e1 e2))) ke m  
      (cure  e1) (kearrbase e2 t ke) m
| esid_step :
  forall (e:expr) (id id':ident) (t:type) (dl:decllist) (ke:exprcont) (m:smem) d,
    evaltype e m = Some (Tstruct id' dl) -> ftype id dl = Some t -> 
    estep d (cure (efield e id)) ke m (cure (eaddrof (efield e id)))
      (kederef t ke) m
| eaelem_step :
  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem) d,
    evaltype e1 m = Some (Tarray t n) ->  
    estep d (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
      (kederef t ke) m
| eaptrelem_step :
  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem) d,
    evaltype e1 m = Some (Tptr t) ->  
    estep d (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
      (kederef t ke) m
| euopstep :
  forall (e:expr) (t:type) (op1:uop) (ke:exprcont) (m:smem) d,
    evaltype e m = Some t ->  
    estep d (cure (eunop op1 e)) ke m (cure e) (keop1 op1 t ke) m
| ebop_step:
  forall (e1 e2:expr) (t1 t2:type) (op2:bop) (ke:exprcont) (m:smem) d,
    evaltype e1 m = Some t1 -> evaltype e2 m =Some t2 ->  
    estep d (cure (ebinop op2 e1 e2)) ke m (cure e1) (keop2r op2 e2 t1 t2 ke) m
| ecast_step:
  forall (e:expr) (t t' t'': type) (m:smem) (ke:exprcont) d,
    t=Tptr t' -> evaltype e m = Some (Tptr t'') ->  
    estep d (cure (ecast e t)) ke m (cure e) ke m
| ecastnull_step:
  forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) d,
    t=Tptr t' -> evaltype e m = Some Tnull ->  
    estep d (cure (ecast e t)) ke m (cure e) ke m
| ecastcomptr_step:
  forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) x d,
    t = Tptr t' -> evaltype e m = Some (Tcom_ptr x) ->  
    estep d (cure (ecast e t)) ke m (cure e) ke m
| ecastint_step:
  forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) d,
    evaltype e m = Some t' -> is_int_type t = true -> is_int_type t' = true ->  
    estep d (cure (ecast e t)) ke m (cure e) (kecast t' t ke) m
| evcastint_step:
  forall v v' ke t t' m d,
    cast_eval v t t' = Some v' ->
    estep d [Vint32 v] (kecast t t' ke) m [Vint32 v'] ke m
| evderef_step :
  forall (genv lenv:env) (M:mem) (a:addrval) (v:val) (t:type) (m:smem) (ke:exprcont) d,
    m= (genv, lenv, M) -> load_pt t M (addrval_to_addr a) d = Some v -> 
    estep d [Vptr a] (kederef t ke) m  [v] ke m
| evoff_step :
  forall (b:block) (i i':int32) (ke:exprcont) (m:smem) d,
    estep d [Vptr (b, i)] (keoffset i' ke) m [Vptr (b, (Int.add i i'))] ke m 
| evaddrelem_step :
  forall (v:val) (e:expr) (t:type) (ke:exprcont) (m:smem) d,
    estep d [v] (kearrbase e t ke) m (cure e) (kearrindex v t ke) m
| evaddrv_step:
  forall (v:val) (b:block) (i i' i'':int32) (t:type) (ke:exprcont) (m:smem) d,
    v = Vint32 i'' -> i'= Int.repr (Z_of_nat (typelen t)) ->
    estep d  [v] (kearrindex (Vptr (b, i)) t ke) m
      [Vptr ( b, (Int.add i (Int.mul i' i'')))] ke m
| evuop_step :
  forall (op1:uop) (v v':val) (ke:exprcont) (m:smem) (t:type) d,
    uop_eval v op1 = Some v' -> 
    estep d [v] (keop1 op1 t ke) m [v'] ke m
| evbop1_step :
  forall (op2:bop) (e:expr) (v:val) (t1 t2:type) (ke:exprcont) (m:smem) d,
    estep d [v] (keop2r op2 e t1 t2 ke) m
      (cure e) (keop2l op2 v t1 t2 ke) m
| evbop2_step :
  forall (op2:bop) (v v' v'':val) (t1 t2 :type) (ke:exprcont) (m:smem) d,
    bop_eval v' v t1 t2 op2=Some v'' -> 
    estep d [v] (keop2l op2 v' t1 t2 ke) m  [v'']  ke m.



Definition alloc_pt
  (x : var) (t : type) (e : env) (m : mem) (e' : env) (m':mem) (d: taskdom) : Prop :=  
  exists b,
    addr_in_dom (b, 0%Z) d = true 
    /\ fresh m b /\ m' = allocb m b 0 (typelen t) 
    /\ ~ indom e x /\ e' = set e x (b, t). 


Inductive sstep:
  progunit -> taskdom -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> Prop :=
(*Assign Steps*)

| sassign_step:
  forall (e1 e2:expr) (t1 t2:type) (ks:stmtcont) (m:smem) (p:progunit) d,
    evaltype e1 m = Some t1 -> 
    evaltype e2 m = Some t2 -> 
    assign_type_match t1 t2 ->
    sstep p d (curs (sassign e1 e2)) ks m (cure e2) (kassignr e1 t1 ks) m
          
| sassignrv_step :
  forall (m:smem) (p:progunit) (v:val) (e:expr) (t:type) (ks:stmtcont) d,
    sstep p d [v] (kassignr e t ks) m (cure (eaddrof e))(kassignl v t ks) m
          
| sassignend_step :
  forall (m m': smem) (ge le: env) (M M': mem) (a: addrval) (v: val) 
         (p: progunit) (ks: stmtcont) (t: type) d, 
    m = (ge, le, M) -> 
    m'= (ge, le, M') ->
    addrval_in_dom a d = true -> 
    store t M (addrval_to_addr a) v = Some M' -> 
    sstep p d [Vptr a] (kassignl v t ks) m (curs (sskip None)) ks m' 

(*Function call Steps*)
| scalle_step:
  forall (p:progunit) (e:expr) (t:type) (m:smem) (f:fid) (ks:stmtcont) (el:exprlist) d,
    evaltype e m = Some t ->
    sstep p d (curs (scalle e f el)) ks m (curs (scall f el))(kassignr e t ks) m

| spcall_step :
  forall (p:progunit) (t:type) (e:expr) (el:exprlist) (m:smem) (ks:stmtcont) (f:fid) d, 
    evaltype e m =Some t ->
    sstep p d (curs (scall f (cons e el))) ks m (cure e) (kfuneval f nil (t::nil) el ks) m

| snpcall_step :
  forall (m:smem)(f:fid) (p:progunit) (ks: stmtcont) d,
    sstep p d (curs (scall f nil)) ks m (curs (sfexec f nil nil)) ks m

| svfeval_step:
  forall (p:progunit) (v:val) (e:expr) (vl:vallist)
         (el:exprlist) (ks:stmtcont) (m:smem) (f:fid) (tl:typelist) (t:type) d,
    evaltype e m = Some t -> 
    sstep p d [v] (kfuneval f vl tl (cons e el) ks) m 
      (cure e) (kfuneval f (cons v vl) (t::tl) el ks) m

| svfevalnil_step:
  forall (p:progunit) (v:val) (vl:vallist) (ks:stmtcont) (m:smem) (f:fid) tl d, 
    sstep p d [v] (kfuneval f vl tl nil ks) m (curs (sfexec f (cons v vl ) tl)) ks m

| sfexec_step :
  forall (m m' :smem) (ge le:env) (M:mem) (p:progunit)
         (t:type) (d1 d2:decllist) (s:stmts) (ks:stmtcont) (vl:vallist) (f:fid) tl d, 
    m = (ge, le, M) -> 
    m' = (ge, emp, M) -> 
    p f = Some (t, d1, d2, s)->  
    tlmatch (List.rev tl) d1  -> 
    tl_vl_match tl vl = true ->
    sstep p d (curs (sfexec f vl tl)) ks m (curs (salloc vl (revlcons d1 d2))) 
      (kcall f  s le ks) m'

| sallocp_step :
  forall (m m':smem) (ge le le':env) (M M' M'':mem)
         (b:block) (v:val) (p:progunit) 
         (vl:vallist) (dl:decllist) (ks:stmtcont) (x:var) (t:type) d, 
    m = (ge, le, M) -> 
    m' = (ge, le', M'') ->
    alloc_pt x t le M le' M' d ->  
    get le' x = Some (b,t) -> 
    store t M' (b, 0%Z) v = Some M'' ->
    sstep p d (curs (salloc  (cons v vl) (dcons x t dl))) ks m (curs (salloc  vl dl)) ks m'

| salloclv_step :
  forall (m m':smem) (ge le le':env) (M M':mem) (t:type) (x:var) (p:progunit)
         (dl:decllist) (ks:stmtcont) d,
    m = (ge, le, M) -> 
    m' = (ge,le', M') ->
    alloc_pt x t le M le' M' d -> 
    sstep p d (curs (salloc  nil (dcons x t dl))) ks m (curs (salloc  nil dl)) ks m' 
          
| sallocend_step:
  forall (p:progunit) (f :fid) (s:stmts) (ks:stmtcont) (m:smem) (E:env) d,
    sstep p d (curs (salloc  nil dnil)) (kcall f s E ks) m (curs s) (kcall f s  E ks) m

| sret_step:
  forall (p:progunit) (m:smem) (M:mem) (ge le le':env) (f :fid)
         (ks ks':stmtcont)  (al:freelist) (s: stmts) d,
    m = (ge, le, M) -> 
    callcont ks =Some (kcall f s le' ks') ->
    getaddr le = al ->
    sstep p d (curs sret) ks m (curs (sfree al None)) ks m

| srete_step :
  forall (p:progunit) (ks:stmtcont) (e:expr) (m:smem) d,
    sstep p d (curs (srete e)) ks m (cure e) (kret ks) m

| sretv_step:
  forall (p:progunit) (m:smem) (le ge:env) (M:mem) (ks:stmtcont) (f:fid)  
         (al:freelist) (v:val) (s : stmts) d,
    m = (ge, le, M) ->
    callcont ks <> None -> 
    getaddr le = al ->
    sstep p d [v] (kret ks) m (curs (sfree al (Some v))) ks m 

| sfree_step :
  forall (m m': smem) (le ge: env) (M M': mem) (b: block) (t: type) (p: progunit) 
         (al: freelist) (ks: stmtcont) (v: option val) d, 
    m = (ge, le, M) -> 
    m' = (ge, le , M') -> 
    addr_in_dom (b, 0%Z) d = true -> 
    free t b M = Some M' -> 
    sstep p d (curs (sfree (cons (pair b t) al) v)) ks m 
      (curs (sfree al v)) ks m'

| sfreeend_step :
  forall (p:progunit) (ks ks':stmtcont) (m m':smem)
         (ge le le':env) (M:mem) (s : stmts)(f:fid) (v:option val) d,
    m= (ge, le, M) -> 
    m' = (ge, le', M) -> 
    callcont ks =Some (kcall f  s le' ks') ->
    sstep p d (curs (sfree nil v)) ks m (curs (sskip v)) ks' m'

(*Sequential Step*)    
| sseq_step :
  forall (s1 s2:stmts) (ks:stmtcont) (m:smem) (p:progunit) d,
    sstep p d (curs (sseq s1 s2)) ks m (curs s1) (kseq s2 ks) m

| svseq_step :
  forall (p:progunit) (v:val) (s:stmts) (ks:stmtcont) (m:smem) d,
    sstep p d [v] (kseq s ks) m (curs s) ks m 

| sskip_step :
  forall (s:stmts) (ks:stmtcont) (m:smem) (p:progunit) d,
    sstep p d SKIP (kseq s ks) m (curs s) ks m

(*If then else Step*)
| sif_step :
  forall (e:expr) (s1 s2 :stmts) (ks:stmtcont) (m:smem) (p:progunit) d,
    sstep p d (curs (sif e s1 s2)) ks m (cure e) (kif s1 s2 ks) m

| sifthen_step:
  forall  (e:expr) (s :stmts) (ks:stmtcont) (m:smem) (p:progunit) d,
    sstep p d (curs (sifthen e s)) ks m (cure e) (kif s (sskip None) ks) m

| svift_step:
  forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem) d,
    istrue v = Some true ->
    sstep p d (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s1) ks m
          
| sviff_step:
  forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem) d,
    istrue v = Some false ->
    sstep p d (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s2) ks m

(*While Step*)

| swhile_step :
  forall (e:expr) (s:stmts) (ks:stmtcont) (m:smem) (p:progunit) d,
    sstep p d (curs (swhile e s)) ks m (cure e) (kwhile e s ks) m

| svwhilet_step:
  forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem) d,
    istrue v = Some true ->
    sstep p d (curs (sskip (Some v))) (kwhile e s ks) m (curs s) (kseq (swhile e s) ks) m 

| svwhilef_step:
  forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem) d,
    istrue v = Some false ->
    sstep p d (curs (sskip (Some v))) (kwhile e s ks) m SKIP ks m.


Inductive cstep: progunit -> taskdom -> code -> smem -> code -> smem -> Prop :=
| expr_step :
  forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
         (ke ke':exprcont) (ks:stmtcont) d,
    C = (c, ( ke, ks)) -> 
    estep d c ke m c' ke' m' ->
    cstep p d C m (c', ( ke', ks)) m'
| stmt_step :
  forall (p:progunit) (C:code) (m m':smem) (c c':cureval) (ks ks':stmtcont) d,
    C = (c, (kenil, ks)) -> 
    sstep p d c ks m c' ks' m' ->
    cstep p d C m (c', (kenil , ks')) m'.


Inductive cstepstar: progunit -> taskdom -> code -> smem -> code -> smem -> Prop := 
| c_stepstar0:
  forall (p:progunit) (C:code) (m:smem) d,
    cstepstar p d C m C m
| c_stepstarn:
  forall (p:progunit) (C C' C'':code) (m m' m'':smem) d,
    cstep p d C m C' m' ->
    cstepstar p d C' m' C'' m'' -> 
    cstepstar p d C m C'' m''.


(****)
Definition eqdomtls (tls tls':TcbMod.map) :=
  forall tid, indom tls tid <-> indom tls' tid.
  
(* Definition eqdomO (O O':osabst) := *)
(*   (forall (x:absdataid), indom O x <-> indom O' x) /\ *)
(*     ( forall tls,  get O abstcblsid = Some (abstcblist tls) -> *)
(*                    exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls' ). *)

(* Inductive absdata :=  *)
(* | abstcblist: TcbMod.map -> absdata *)
(* | absecblist : EcbMod.map -> absdata *)
(* | ostm: ostime -> absdata *)
(* | oscurt: addrval -> absdata *)
(* | hier: Hier -> absdata *)
(* | hinthandler: Hinthandler -> absdata *)
(* | hinthandlerParam: HinthandlerParam -> absdata *)
(* | hexchandler: Hexchandler -> absdata *)
(* (* add by CNU *) *)
(* | absptls: PtbMod.map -> absdata (* ostcbpriotbl *) *)
(* | seminfo: EmbMod.map -> absdata (* gjb seminfo *) *)
(* | absmutinfo: MibMod.map -> absdata (* gjb mutexinfo*) *)
(* | absmqattr: MqattrMod.map -> absdata (* gjb mqattr *) *)
(* | pblist: PbMod.map -> absdata (* pos list *) *)
(* | eblist: errmp -> absdata (* one err list per domain *)   *)
(* | evatomheap: ( list (addrval * type * val) )  -> absdata (* atom heaps *) *)
(* | evstructheap: ( list (addrval * type * (list val)) )  -> absdata (* struct heaps *) *)
(* | evarrayheap: ( list (addrval * nat * (list val)) )  -> absdata (* array heaps *) *)
(* | evloc: EvAuxLocMod.map -> absdata (* auxliary event location *) *)
(* | evptr: EvAuxPtrMod.map -> absdata (* auxliary event pointer *) *)
(* | ksdschedidx:  ksdscdidx  -> absdata (* KsDomScheduleIdx *) *)
(* | ksdschedlen:  ksdscdlen  -> absdata (* KsDomScheduleLength *) *)
(* | kscurdom: kscur  -> absdata (* KsCurDomain *) *)
(* | kslastdom: kslast  -> absdata (* KsLastDomain *) *)
(* | ksdomtime: ksdtime  -> absdata (* KsDomainTime *) *)
(* | ksdsched: KsDScdMod.map  -> absdata (* KsDomSchedule[idx] *) *)
(* | domindexlist: Dom2IdxMod.map -> absdata (* Domain2Index *) *)
(* | absuconf: absucosconf -> absdata (* ucos_conf_t *) *)
(* | intparmux: IntPMuxMod.map -> absdata (* IntPartitionMux *) *)
(* | domtlist:  DomTMod.map -> absdata *)
(* (* end add by CNU *)  *)
(* (* add by SJTU *)  *)
(* | ostmr : option TmrMod.map -> absdata *)
(* | osrate : osclkrate -> absdata *)
(* | oscurtcore : coreid -> absdata *)
(* | oscoreheap : ( list (addrval * nat * (list val)) * list (addrval * type * val ) * list (addrval * type * (list val)))  -> absdata *)
(* | ossend : list (list val) -> absdata *)
(* | osrecv : list (list val) -> absdata *)
(* | osipcsem : list ecbid  -> absdata *)
(* | osipcsendsem : list ecbid -> absdata *)
(* | osipcsemshared : ecbid -> absdata  *)
(* | osipcbroad : list coreid -> absdata *)
(* | osipcgr: val -> absdata *)
(* (* end add by SJTU *)  *)
(* (* add for Partition *) (* from partsjtu *)  *)
(* | oskport : KernelPMod.map -> absdata  (*0-PORTNUM*) *)
(* | oschannel : ChannelMod.map -> absdata *)
(* | osdomainport : DomainPortMod.map -> absdata *)
(* (* add by CNU *) *)
(* | ibufs: bufmp -> absdata *)
(* | obufs: bufmp -> absdata                      *)
(* . *)

(* Definition ty_map (x: absdataid) := *)
(*   if absdataid_eq x abstcblsid then *)
(*     TcbMod.map *)
(*   else if absdataid_eq x absecblsid then  *)
(*          EcbMod.map *)
(*        else if absdataid_eq x ostmid then *)
(*               ostime *)

(* Definition dom_impl (O O': osabst) := *)
(*   forall (x: absdataid), *)
(*     match get O x with *)
(*       Some (C y) => exists y', get O' x = Some (C y') *)
(*     | _ => False *)
(*     end. *)
  
Definition dom_impl (O O': osabst) :=
  forall (x: absdataid),
    match get O x with
      Some (abstcblist _) => exists y, get O' x = Some (abstcblist y)
    | Some (absecblist _ ) => exists y, get O' x = Some (absecblist y)
    | Some (ostm _) => exists y, get O' x = Some (ostm y)
    | Some (oscurt _) => exists y, get O' x = Some (oscurt y) 
    | Some (hier _) => exists y, get O' x = Some (hier y)  
    | Some (hinthandler _) => exists y, get O' x = Some (hinthandler y)
    | Some (hinthandlerParam _) => exists y, get O' x = Some (hinthandlerParam y) 
    | Some (hexchandler _) => exists y, get O' x = Some (hexchandler y)
    | Some (absptls _) => exists y, get O' x = Some (absptls y) 
    | Some (seminfo _) => exists y, get O' x = Some (seminfo y) 
    | Some (absmutinfo _) => exists y, get O' x = Some (absmutinfo y) 
    | Some (absmqattr _) => exists y, get O' x = Some (absmqattr y) 
    | Some (pblist _) => exists y, get O' x = Some (pblist y) 
    | Some (eblist _) => exists y, get O' x = Some (eblist y) 
    | Some (evatomheap _) => exists y, get O' x = Some (evatomheap y) 
    | Some (evstructheap _) => exists y, get O' x = Some (evstructheap y) 
    | Some (evarrayheap _)  => exists y, get O' x = Some (evarrayheap y)
    | Some (evloc _) => exists y, get O' x = Some (evloc y) 
    | Some (evptr _) => exists y, get O' x = Some (evptr y) 
    | Some (ksdschedidx _) => exists y, get O' x = Some (ksdschedidx y)
    | Some (ksdschedlen _) => exists y, get O' x = Some (ksdschedlen y) 
    | Some (kscurdom _) => exists y, get O' x = Some (kscurdom y) 
    | Some (kslastdom _) => exists y, get O' x = Some (kslastdom y) 
    | Some (ksdomtime _) => exists y, get O' x = Some (ksdomtime y)  
    | Some (ksdsched _) => exists y, get O' x = Some (ksdsched y) 
    | Some (domindexlist _) => exists y, get O' x = Some (domindexlist y) 
    | Some (absuconf _) => exists y, get O' x = Some (absuconf y) 
    | Some (intparmux _) => exists y, get O' x = Some (intparmux y) 
    | Some (domtlist _) => exists y, get O' x = Some (domtlist y)
    | Some (ostmr _) => exists y, get O' x = Some (ostmr y)
    | Some (osrate _) => exists y, get O' x = Some (osrate y) 
    | Some (oscurtcore _) => exists y, get O' x = Some (oscurtcore y) 
    | Some (oscoreheap _) => exists y, get O' x = Some (oscoreheap y) 
    | Some (ossend _) => exists y, get O' x = Some (ossend y) 
    | Some (osrecv _) => exists y, get O' x = Some (osrecv y) 
    | Some (osipcsem _) => exists y, get O' x = Some (osipcsem y)  
    | Some (osipcsendsem _) => exists y, get O' x = Some (osipcsendsem y)   
    | Some (osipcsemshared _) => exists y, get O' x = Some (osipcsemshared y)    
    | Some (osipcbroad _) => exists y, get O' x = Some (osipcbroad y) 
    | Some (osipcgr _) => exists y, get O' x = Some (osipcgr y)   
    | Some (oskport _) => exists y, get O' x = Some (oskport y)    
    | Some (oschannel _) => exists y, get O' x = Some (oschannel y)     
    | Some (osdomainport _) => exists y, get O' x = Some (osdomainport y)  
    | Some (ibufs _) => exists y, get O' x = Some (ibufs y)  
    | Some (obufs _) => exists y, get O' x = Some (obufs y)   
    | Some (capcspace _) => exists y, get O' x = Some (capcspace y) 
    | None => get O' x = None
    end.

(* Definition eqdomO0 O O' := *)
(*   forall (x: absdataid) (ty: Type) (C: ty -> absdata), *)
(*     (exists (y: ty), get O x = Some (C y)) <-> (exists (y': ty), get O' x = Some (C y')).  *)

Definition eqdomO0 O O' :=
  dom_impl O O' /\ dom_impl O' O.

Definition eqdomO (O O': osabst) :=
  eqdomO0 O O' /\ 
    (forall tls,  get O abstcblsid = Some (abstcblist tls) ->
                  exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls').

Definition tidsame (O O':osabst) :=  get O curtid =  get O' curtid.

Parameter chsem_res: osabst -> val -> Prop. 

Inductive spec_step: ossched -> spec_code -> osabst -> spec_code -> osabst -> action -> Prop :=
| spec_prim_step:
    forall sc O O' (step:osabstep) v Of vl OO OO' act asrt,
      step vl O act (v, Some O') ->
      eqdomO O O' ->
      tidsame O O' ->
      join O Of OO ->
      join O' Of OO' ->
      spec_step sc (spec_prim asrt vl step) OO (spec_done v) OO' act 
                
| spec_prim_step_abt:
    forall sc O (step:osabstep) v Of vl OO act asrt, 
      step vl O act (v, None) -> 
      join O Of OO ->
      spec_step sc (spec_prim asrt vl step) OO spec_abort OO TauAct
  
| spec_seq_step_end:
    forall v s1 s2 O O' sc act,
      spec_step sc s1 O (spec_done v) O' act ->
      spec_step sc (spec_seq s1 s2) O s2 O' act

| spec_seq_step_abt:
  forall s1 s2 O O' sc act,
    spec_step sc s1 O spec_abort O' act -> 
    spec_step sc (spec_seq s1 s2) O spec_abort O TauAct

| spec_seq_step_ok:
    forall O O' s1 s2 s1' sc act,
      spec_step sc s1 O s1' O' act ->
      ((~exists vo, s1' = spec_done vo) /\ s1' <> spec_abort) -> 
      spec_step sc (spec_seq s1 s2) O (spec_seq s1' s2) O' act

| spec_ifelse_step1:
    forall OO OO' (b: absexpr) s1 s2 s1' sc act asrt,
      b OO ->
      spec_step sc s1 OO s1' OO' act -> 
      spec_step sc (spec_ifelse asrt b s1 s2) OO s1' OO' act

| spec_ifelse_step2:
    forall OO OO' (b: absexpr) s1 s2 s2' sc act asrt,
      ~ b OO ->
      spec_step sc s2 OO s2' OO' act -> 
      spec_step sc (spec_ifelse asrt b s1 s2) OO s2' OO' act 

| spec_if_else_step1:
  forall OO (b: absexpr) s1 s2 sc asrt,
    b OO ->
    spec_step sc (spec_if_else_ asrt b s1 s2) OO s1 OO TauAct

| spec_if_else_step2:
  forall OO (b: absexpr) s1 s2 sc asrt,
    ~ b OO ->
    spec_step sc (spec_if_else_ asrt b s1 s2) OO s2 OO TauAct

| spec_assume_step:
    forall O Of (b:absexpr) OO sc asrt,
      b O ->
      join O Of OO ->
      spec_step sc (spec_assume asrt b)  OO  (spec_done None) OO TauAct

| spec_assert_step_cont:
  forall O Of (b:absexpr) OO sc asrt,
    b O ->
    join O Of OO ->
    spec_step sc (spec_assert asrt b) OO (spec_done None) OO TauAct

| spec_assert_step_abt:
    forall O Of (b:absexpr) OO sc asrt,
      ~(b O) ->
      join O Of OO -> 
      spec_step sc (spec_assert asrt b) OO spec_abort OO TauAct
                
| spec_sched_step:
    forall t O Of OO (sc:ossched) asrt,
      get O curtid = Some (oscurt t) ->
      sc O t -> 
      join O Of OO ->
      spec_step sc (sched asrt) OO (spec_done None) OO TauAct

| spec_cslsemacc_step: 
  forall sc O Of OO n m asrt,
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    chsem_res OO m -> 
    (* (m = Vint32 Int.zero \/ m = Vint32 Int.one) -> *)
    join O Of OO ->
    spec_step sc (cslsemacc asrt n m) OO (spec_done None) OO TauAct

| spec_cslsemrel_step:
    forall sc O Of OO n asrt,
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    join O Of OO ->
      spec_step sc (cslsemrel asrt n) OO (spec_done None) OO TauAct 
. 

Inductive hapistep:  osspec -> code -> osabst -> code -> osabst -> action -> Prop :=

| hapienter_step:
    forall (A :osspec) (B:osapispec) (C:osintspec) (D : ossched) (O:osabst) (cd cd':code)
           (ks:stmtcont) (f:fid) (vl:vallist) r tl tp vl',
      A = (B, C, D) ->
      tl_vl_match tl vl = true->
      cd = (curs (sfexec f (List.rev vl) (List.rev tl)), (kenil, ks)) ->
      cd' = (curs (hapi_code (r (vl++vl'))), (kenil, ks))->
      B f = Some (r,(tp,tl)) ->
      hapistep  A cd O cd' O TauAct
                
| hidapi_step :
    forall (A :osspec) (O O':osabst) ke ks cd cd' act,
      spec_step (snd A) cd O cd' O' act ->
      hapistep A ((curs (hapi_code cd )),(ke, ks)) O ((curs (hapi_code cd')),(ke,ks)) O' act 

| hapiexit_step :
  forall (A :osspec) (O:osabst) ke ks v,
    (* here we express that there is no interrupt handling in the continuation *)
    (* this makes the semantics deterministic *) 
      absintcont ks = None -> 
      hapistep A ((curs (hapi_code (spec_done v))),(ke, ks)) O ((curs (sskip v)),(ke,ks)) O TauAct
               
| hintex_step: forall  (A :osspec) c ke ks  O,
    hapistep A  (curs (hapi_code (spec_done None)),(kenil,kevent c ke ks)) O
      (c,(ke,ks)) O TauAct.


Inductive htstep :
  hprog -> tid -> taskdom ->
  code -> clientst -> osabst -> code -> clientst -> osabst ->
  action -> Prop := 
  
| htclt_step :
  forall (p: hprog) (pc: progunit) (A: osspec) (c c': code) (m m': smem)
         (cenvs: cltenvs)  (ge le le': env) (M M': mem) (t: tid) 
         (cst cst': clientst) (O: osabst) d pr ges,
    p= (pc, A) -> 
    task_prio_id O pr t -> 
    dom_for_prio pr = d -> 

    cstep pc d c m c' m' -> 
    m = (ge, le, M) -> m' = (ge, le', M') ->
    ges d = ge -> 
    get cenvs t = Some le ->
    
    cst = (ges, cenvs, M) ->
    cst' = (ges, (set cenvs t le'), M') -> 
    htstep p t d c cst O c' cst' O TauAct

| hapi_step :
  forall (p: hprog)(A: osspec) (pc: progunit) (O O': osabst) (c c': code) (cst: clientst) t act d,
    p = (pc, A) ->
    hapistep A c O c' O' act -> 
    htstep p t d c cst O c' cst O' act. 


(* The original rule abstracted away the requirement that an
    interrupt at the same level should not be already in service. 
    We capture this condition using "absintcont ks = None" since the
    only interrupt in the system (for information flow verification) is
    the tick interrupt. *)  
Inductive htistep: osintspec -> code  -> osabst -> code  -> osabst -> Prop :=
| hinten_step:
  forall  (C: osintspec)  (O: osabst) c ke ks (i: hid) l,
    C i = Some l ->
    absintcont ks = None -> 
    htistep C (c,(ke,ks)) O (curs (hapi_code l), (kenil, kevent c ke ks)) O.



Inductive hpstep:
  hprog -> tasks -> clientst -> osabst -> tasks -> clientst -> osabst -> action -> Prop := 
  
| hp_step:
  forall (p: hprog) (T T': tasks) (O O': osabst) (cst cst': clientst) (C C': code) (t: tid) act pr (d: taskdom),  
    get O curtid = Some (oscurt t) -> 
    task_prio_id O pr t -> 
    dom_for_prio pr = d -> 
    htstep p t d C cst O C' cst' O' act -> 
    get T t = Some C -> T' =  set T t C' -> 
    hpstep p T cst O T' cst' O' act 
                    
| hi_step :
  forall (p: hprog) pc A  ispec B  (T T': tasks) (O O': osabst) (cst: clientst) (C C': code) (t: tid), 
    p = (pc, (A, ispec, B)) -> 
    get O curtid = Some (oscurt t) -> 
    get T t = Some C ->
    T' =  set T t C' ->
    htistep ispec C O C' O' ->
    hpstep p T cst O T' cst O' EniAct 
                     
| hswi_step :
  forall (p: hprog) pc A B sd (T T': tasks) (cst: clientst) (O: osabst) (t t': tid) C ke ks s asrt,
    p = (pc, (A, B, sd)) -> 
    sd O t' ->
    get O curtid = Some (oscurt t) ->
    get T t = Some C ->
    C = (curs (hapi_code (spec_seq (sched asrt) s)), (ke,ks)) ->
    T' =  set T t (curs (hapi_code s),(ke,ks)) ->
    hpstep p T cst O T' cst (set O curtid (oscurt t')) SchAct 
           
(* | hpcrt_step : *)
(*   forall (T: tasks) (O O': osabst) (t t': tid) *)
(*          (s: stmts) (cst cst': clientst) *)
(*          (pc: progunit) (A: osspec) (tau: type) (d1 d2: decllist)  *)
(*          (C C': code) f tls tls' v1 v2 v3 ge le M M' cenvs ke ks scre sus pr d ges asrt,  *)
(*     get T t = Some C -> *)
(*     C = (curs (hapi_code (spec_seq (spec_crt asrt v1 v2 (Vint32 v3)) scre)), (ke,ks)) -> *)
(*     C' = (curs (hapi_code scre), (ke, ks)) -> *)
(*     get O curtid = Some (oscurt t) -> *)
    
(*     vtoZ v1 = Some f -> *)
    
(*     pc f = Some (tau, d1, d2, s)-> *)
(*     task_prio_id O pr t -> *)
(*     dom_for_prio pr = d ->  *)
(*     cstepstar pc d *)
(*       ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) *)
(*       (ge,emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M') -> *)
(*     cst = (ges, cenvs, M) -> *)
(*     cst'=(ges, (set cenvs t' le), M') -> *)
(*     ge = ges d ->  *)
                 
(*     get O abstcblsid = Some (abstcblist tls) -> *)
(*     set O abstcblsid (abstcblist tls') = O' -> *)
(*     join tls (sig t' (v3, rdy, Vnull, sus, v3)) tls' -> *)

(*     dom_for_prio v3 = d ->  *)
    
(*     hpstep (pc, A) T cst O (set ( set T t C') t' (nilcont s)) cst' O' TauAct  *)

(* | hpcrtskip_step : *)
(*   forall (T: tasks) (O O': osabst) (t t': tid) (cst: clientst) *)
(*          C C' (pc: progunit) (A: osspec) *)
(*          f tls tls' v1 v2 v3 ge M cenvs ke ks scre sus (pr: priority) (d: taskdom) ges asrt, *)
(*     get T t = Some C -> *)
(*     C = (curs (hapi_code (spec_seq (spec_crt asrt v1 v2 (Vint32 v3)) scre)), (ke,ks)) -> *)
(*     C' = (curs (hapi_code scre), (ke, ks)) -> *)
(*     get O curtid = Some (oscurt t) -> *)
    
(*     vtoZ v1 = Some f -> *)

(*     task_prio_id O pr t -> *)
(*     dom_for_prio pr = d -> *)
    
(*     (pc f = None \/  *)
(*        (exists t d1 d2 s, *)
(*            pc f = Some (t ,d1,d2,s) /\ *)
(*              ~(exists le M', *)
(*                    cstepstar pc d *)
(*                      ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) *)
(*                      (ge, emp, M) *)
(*                      ((curs s), (kenil, (kcall f s emp kstop))) *)
(*                      (ge, le, M')))) -> *)
    
(*     cst = (ges, cenvs, M) -> *)
(*     ge = ges d ->  *)
    
(*     get O abstcblsid = Some (abstcblist tls) -> *)
(*     set O abstcblsid (abstcblist tls') = O' -> *)
(*     join tls (sig t' (v3, rdy, Vnull, sus, v3)) tls' ->   *)

(*     dom_for_prio v3 = d ->  *)

(*     hpstep (pc, A) T cst O *)
(*       (set ( set T t C') t' (nilcont (sskip None))) cst O' TauAct  *)
      
(* | hpdel_step: *)
(*   forall p T T' t t' C C' sdel ke ks ge cenvs M O O' tls tls' cst cst' prio st msg pr sus pr0 asrt, *)
                
(*     get T t = Some C -> *)
(*     C = (curs (hapi_code (spec_seq (spec_del asrt (Vint32 pr0)) sdel)), (ke, ks)) -> *)
(*     C' = (curs (hapi_code sdel), (ke, ks)) -> *)
(*     set T t C' = T' -> *)
(*     cst = (ge, cenvs, M) -> *)
(*     cst' = (ge, (del cenvs t'), M) -> *)
(*     get O abstcblsid = Some (abstcblist tls) -> *)
(*     set O abstcblsid (abstcblist tls') = O' -> *)
(*     get tls t' = Some (prio, st, msg, sus, pr0) -> *)
(*     join tls' (sig t' (prio, st, msg, sus, pr0)) tls -> *)
(*     get O curtid = Some (oscurt t) -> *)

(*     task_prio_id O pr t -> *)
(*     dom_for_prio pr = dom_for_prio pr0 ->  *)

(*     hpstep p T cst O T' cst' O' TauAct *).


Definition code_cur_task (T: tasks) (O: osabst) : option code :=
  match (get O curtid) with
    Some (oscurt t) =>
      match get T t with
        Some TC => Some TC
      | _ => None
      end
  | _ => None
  end.        

Definition in_intr (T: tasks) (O: osabst) : Prop :=
  exists c ke ks,
    code_cur_task T O = Some (c, (ke, ks)) /\ absintcont ks <> None.

Definition nabt (T: tasks) : Prop :=
  forall t c ke ks,
    get T t = Some (c, (ke, ks)) -> c <> curs (hapi_code spec_abort).


Definition hpstep_ok p T cst O T' cst' O' act :=
  hpstep p T cst O T' cst' O' act /\ nabt T'. 
  
Inductive hpstepokstar:
  hprog -> tasks -> clientst -> osabst  -> tasks -> clientst -> osabst  -> Prop:=  
| hp_stepO:
  forall (p:hprog) (T:tasks) (cst:clientst) O,
    hpstepokstar p T cst O  T cst O 
| hp_stepS:
  forall p T T' T'' cst cst' cst'' O O' O'' act,
    hpstep_ok p T cst O T' cst' O' act ->
    hpstepokstar p T' cst' O'  T'' cst'' O''->
    hpstepokstar p T cst O T'' cst'' O'' .


(* steps of the system with the annotation of domains *) 
Inductive hpstep_pt:
  hprog -> tasks -> clientst -> osabst -> tasks -> clientst -> osabst ->
  action -> dom -> Prop :=

  hptskd_step:
    forall hp t T cst O T' cst' O' act pr d, 
      hpstep hp T cst O T' cst' O' act ->
      (act = TauAct \/ act = SendAct \/ act = RecvAct) ->
      (~in_intr T O) -> 
      get O curtid = Some (oscurt t) ->
      task_prio_id O pr t -> 
      dom_for_prio pr = d ->       
      nabt T' -> 
      hpstep_pt hp T cst O T' cst' O' act (TaskDom d) 

| hpschd_step:
  forall hp T cst O T' cst' O' act, 
    hpstep hp T cst O T' cst' O' act ->
    (act = EniAct \/ (act = TauAct /\ in_intr T O)  \/ act = SchAct) -> 
    nabt T' -> 
    hpstep_pt hp T cst O T' cst' O' act SchedDom. 
      
