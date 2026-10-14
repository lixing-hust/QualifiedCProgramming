Require Import memory.
Require Import language.
(*Require Import int_lock.*)
Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.


Definition OSTCBHighRdy:= 59%Z.
Definition OSTCBCur:=60%Z.

Definition gets_g (s:osstate):= (fst (fst (fst (fst (fst s))))).
Definition gets_m (s:osstate) := (snd (fst (fst (fst s)))).
Definition get_env (m:smem):= (snd (fst m)).

Definition Dteq (D1 D2:clientst)(t:tid):Prop:=
  match D1 with 
    | ( _ ,evs1, _) => match D2 with
                         | ( _, evs2, _) =>
                           forall (t':tid), ~(t'=t) ->  get evs1 t' = get evs2 t'
                       end
  end. 

Definition Piteq (pi1 pi2: ltaskstset) (t:tid):Prop:=
  forall (t':tid), ~(t'=t) -> get pi1 t'= get pi2 t'.

Definition Steq (S1 S2 :osstate) (t:tid):Prop:=
  match S1 with
    | (D1, ir, er, pi1)  => match S2 with 
                           | ( D2 , ir', er', pi2) => Dteq D1 D2 t /\ Piteq pi1 pi2 t
                         end
  end.

Definition Dnewt (D:clientst) (t:tid):clientst:=
  match D with 
    | ( ge, cvs,  M) => ( ge, ( set cvs t emp), M)
  end.

Definition Tlnewt (tl:ltaskstset) (t:tid) :ltaskstset:=
  set tl t (true, nil, nil).

Definition Snewt (S:osstate) (t:tid):osstate:=
  match S with
    | (D, ir, er, tl) =>  ((Dnewt D t), ir, er, (Tlnewt tl t))
  end.


Definition projD (D:clientst) (t:tid) := 
  match D with (x,y,z) => 
               match  get y t with
                 | Some e => Some (x, e , z)
                 | _ => None
               end
  end.

Definition projS (S:osstate) (t:tid) :=
  match S with ( x, y, e, z)  =>
               match (projD x t),(get z t) with
                 | Some m,Some n => Some (m , y , e, n)
                 | _,_ => None
               end
  end.


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
    | Tunion _ _, _ => true
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

(*
Definition uop_eval (v:val) (op1:uop):= Some (Vint32 Int.zero).

Definition uop_type (t:type) (op1:uop):= Some t.

Definition bop_eval (v v':val) (op2:bop):= Some (Vint32 Int.zero).

Definition bop_type (t1 t3:type) (op2 :bop):= Some Tint8.
 *)

Definition is_int_type t:=
  match t with
    | Tint8 => true
    | Tint16 => true
    | Tint32 => true
    | _ => false
  end.

Fixpoint evaltype (e:expr) (m:smem){struct e}:option type:=
  match m with 
      (genv, lenv, my) =>
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
                            | Some (Tunion id' dl) => ftype id dl
                            | _=> None
                          end
        | ecast e' t => match evaltype e' m, t with 
                          | Some (Tptr t'), Tptr t'' => Some t
                          | Some Tnull, Tptr t' => Some t
                          | Some (Tcom_ptr t'), Tptr t'' => Some t  
                          | Some Tint8 , Tint8 => Some t
                          | Some Tint8 , Tint16 => Some t
                          | Some Tint8 , Tint32 => Some t
                          | Some Tint16 , Tint8 => Some t
                          | Some Tint16 , Tint16 => Some t
                          | Some Tint16 , Tint32 => Some t
                          | Some Tint32 , Tint8 => Some t
                          | Some Tint32 , Tint16 => Some t
                          | Some Tint32 , Tint32 => Some t
                          | Some Tint32,  Tptr t' => Some t
                          | Some (Tptr t'),  Tint32 => Some t
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
| eq_union: forall t1 t2, (exists id dl, t1= (Tunion id dl) /\ t2 = (Tunion id dl))->
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
    | Some (Tunion id' dl) => Some (b, Int.repr i)
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

Definition load (t : type) (m : mem) (l : addr) : option val :=
  match t with 
    | Tarray _ _ => Some (Vptr (addr_to_addrval l))
    | _ => loadm t m l 
  end.

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

(* content about cast Tint32 to Tptr _ *)

Parameter block_bit : Z.
Parameter block_bit_range :  Z.lt 0 block_bit /\ Z.lt block_bit Int.zwordsize.

Definition offset_bit:= Int.zwordsize - block_bit.
(* all block and offset, at least one bit *)

Definition int32_to_ptr (v: int32) :addrval :=
( Z.to_pos (Int.unsigned (Int.shru v (Int.repr offset_bit))), Int.zero_ext offset_bit v).

Definition ptr_to_int32 (adr: addrval) : int32:=
match adr with (b,i) => Int.or (Int.shl (Int.repr (Z.pos b)) (Int.repr offset_bit) ) (Int.zero_ext offset_bit i)  end.


Fixpoint evalval (e:expr) (m:smem) :option val:= 
  match evaltype e m with
    | Some t =>  
      match e with 
        | enull => Some Vnull
        | econst32 n => Some (Vint32 n)
        | eptrconst a => Some (Vptr a)
        | evar x => match get (get_lenv m) x with
                      | Some (pair a t) => load t (get_mem m) (a,0%Z)
                      | None =>
                        match get (get_genv  m) x with
                          | Some (pair a t) => load t (get_mem m) (a,0%Z)
                          | None => None
                        end
                    end
        | eunop op1 e' =>  match evalval e' m with
                             | Some v=> uop_eval v op1
                             | _ => None
                           end
                             
        | ebinop op2 e1 e2 =>  match evalval e1 m, evalval e2 m with
                                 | Some v1,Some v2 => match evaltype e1 m, evaltype e2 m with
                                                        | Some t1, Some t2 => bop_eval v1 v2 t1 t2 op2
                                                        | _,_ => None
                                                      end 
                                 | _,_ => None
                               end
        | eaddrof e' =>  match e' with
                           | evar x =>  evaladdr e' m 
                           | ederef e'' => evalval e'' m
                           | efield e'' id => evaladdr e' m 
                           | earrayelem e1 e2 => evaladdr e' m 
                           | _ => None
                         end
        | ederef e' => match evalval e' m with
                         | Some (Vptr ad) =>  load t (get_mem  m) (addrval_to_addr ad) 
                         | _ => None
                       end
        | efield e' id => match (evaladdr e' m) with
                            | (Some (Vptr ( b,  i))) => match getoff b (Int.unsigned i) id e' m with
                                                          | Some ad => load t (get_mem m) (addrval_to_addr ad)
                                                          | _ => None
                                                        end
                            | _ => None
                          end
        | ecast e' t' =>
          match evaltype e' m with
            | Some te =>
              match is_int_type te,is_int_type t' with
                | true, true =>
                  match evalval e' m with
                    | Some (Vint32 x) => match (cast_eval x te t') with
                                           | Some x' => Some (Vint32 x')
                                           | None => None
                                         end
                    | _ => None
                  end
                | true, false =>
                   match te, t' with
                     | Tint32, Tptr t'' => match evalval e' m with  (* cast Tint32 to Tptr t *)
                                                                | Some (Vint32 x) => Some (Vptr (int32_to_ptr x))
                                                                | _ => None
                                                              end
                     | _, _ => evalval e' m
                   end
                | false, true =>
                   match te, t' with
                     | Tptr t'', Tint32 => match evalval e' m with  (* cast Tptr to Tint32 *)
                                                                | Some (Vptr x) => Some (Vint32 (ptr_to_int32 x))
                                                                | _ => None
                                                              end
                     | _, _ => evalval e' m
                   end
                | _ , _ => evalval e' m
              end
            | _ => None
          end
        | earrayelem e1 e2 => match (evalval e1 m),(evalval e2 m) with
                                |Some (Vptr ( b,  i)), Some v =>
                                 match v with
                                   | Vint32 z => load t (get_mem m) ( b, Int.unsigned (Int.add i
                                                                                               (Int.mul (Int.repr (Z_of_nat (typelen t))) z )))
                                   |_ => None
                                 end
                                |_,_=>None
                              end
                                
      end
    | _ => None
  end
with evaladdr (e:expr) (m:smem) :option val:=
       match e with
         | evar x => match get (get_lenv m) x with
                       |Some (pair a t) => Some (Vptr (a,Int.zero))
                       |_ => match get (get_genv m) x with
                               |Some (pair a t) => Some (Vptr (a,Int.zero))
                               |_ => None
                             end
                     end
         | ederef e' => evalval e' m
         | efield e' id => match evaladdr e' m with
                             | (Some (Vptr ( b, i))) => match getoff b (Int.unsigned i) id e' m with
                                                          |Some ad => Some (Vptr  ad)
                                                          |_=> None
                                                        end
                             | _ => None
                           end
         | earrayelem e1 e2 => match (evaltype e1 m), (evalval e1 m),(evalval e2 m) with
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

(*
CoInductive infnat :=
| infcons : infnat -> infnat.

Fixpoint inadd (infn:infnat) (n: nat) :infnat:=
  match n with
    | O => infn
    | S n' => inadd (infcons infn) n'
  end.
 *)
Inductive estep: cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop :=
| enull_step : forall m ke,
                 estep (cure enull) ke m [Vnull] ke m
| ec32_step: forall (i:int32) (m:smem) (ke:exprcont), 
               estep (cure (econst32 i)) ke m [Vint32 i] ke m
| eptrc_step: forall a m ke, 
               estep (cure (eptrconst a)) ke m [Vptr a] ke m
| evar_step : forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (evar x) m =Some v ->  estep (cure (evar x)) ke m [v] ke m
| eaddr_step: forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (eaddrof (evar x)) m = Some v ->  
                estep (cure (eaddrof (evar x))) ke m [v] ke m
| ederef_step: forall (e:expr) (t:type) (m:smem) (ke:exprcont),
                 evaltype e m = Some (Tptr t) -> 
                 estep (cure (ederef e)) ke m (cure e) (kederef t ke) m
| eaddrderef_step: forall e m ke,
                     estep (cure (eaddrof (ederef e))) ke m (cure e) ke m
| esidaddr_step_struct: forall (e:expr) (id id':ident) i (dl:decllist) (ke:exprcont) (m:smem),
                   evaltype e m = Some (Tstruct id' dl) ->
                   field_offset id dl = Some i -> 
                   estep (cure (eaddrof (efield e id))) ke m (cure (eaddrof e))
                         (keoffset i ke) m
| esidaddr_step_union: forall (e:expr) (id id':ident) (dl:decllist) (ke:exprcont) (m:smem),
                         evaltype e m = Some (Tunion id' dl) ->
                         estep (cure (eaddrof (efield e id))) ke m (cure (eaddrof e))
                               (keoffset (Int.repr 0) ke) m
| eaptrelemaddr_step:  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                         evaltype e1 m = Some (Tptr t) ->  
                         estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                               (cure e1) (kearrbase e2 t ke) m
| eaelemaddr_step:  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tarray t n) ->  
                      estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                            (cure  e1) (kearrbase e2 t ke) m
| esid_step : forall (e:expr) (id id':ident) (t:type) (dl:decllist)
                     (ke:exprcont) (m:smem),
                evaltype e m = Some (Tstruct id' dl) \/ evaltype e m = Some (Tunion id' dl)
                -> ftype id dl = Some t -> 
                estep (cure (efield e id)) ke m (cure (eaddrof (efield e id)))
                      (kederef t ke) m
| eaelem_step :  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                   evaltype e1 m = Some (Tarray t n) ->  
                   estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                         (kederef t ke) m
| eaptrelem_step :  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tptr t) ->  
                      estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                            (kederef t ke) m
| euopstep:  forall (e:expr) (t:type) (op1:uop) (ke:exprcont) (m:smem),
               evaltype e m = Some t ->  
               estep (cure (eunop op1 e)) ke m (cure e) (keop1 op1 t ke) m
| ebop_step:  forall (e1 e2:expr) (t1 t2:type) (op2:bop) (ke:exprcont) (m:smem),
                evaltype e1 m = Some t1 -> evaltype e2 m =Some t2 ->  
                estep (cure (ebinop op2 e1 e2)) ke m (cure e1) (keop2r op2 e2 t1 t2 ke) m
| ecast_step: forall (e:expr) (t t' t'': type) (m:smem) (ke:exprcont),
                t=Tptr t' -> evaltype e m = Some (Tptr t'') ->  
                estep (cure (ecast e t)) ke m (cure e) ke m
| ecastnull_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                    t=Tptr t' -> evaltype e m = Some Tnull ->  
                    estep (cure (ecast e t)) ke m (cure e) ke m
| ecastcomptr_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) x,
                      t = Tptr t' -> evaltype e m = Some (Tcom_ptr x) ->  
                      estep (cure (ecast e t)) ke m (cure e) ke m
| ecastint_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                   evaltype e m = Some t' -> is_int_type t = true -> is_int_type t' = true ->  
                   estep (cure (ecast e t)) ke m (cure e) (kecast t' t ke) m
| evcastint_step: forall v v' ke t t' m,
                    cast_eval v t t' = Some v' ->
                    estep [Vint32 v] (kecast t t' ke) m [Vint32 v'] ke m

| ecastint_ptr_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                   t = Tptr t' -> evaltype e m = Some Tint32 ->
                   estep (cure (ecast e t)) ke m (cure e) (kecast (Tptr t') Tint32 ke) m
| evcastint_ptr_step: forall v (t: type) (m:smem) (ke:exprcont),
                   estep [Vint32 v] (kecast (Tptr t) Tint32 ke) m [Vptr (int32_to_ptr v)] ke m

| ecastptr_int_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                   t = Tint32 -> evaltype e m = Some (Tptr t') ->
                   estep (cure (ecast e t)) ke m (cure e) (kecast Tint32 (Tptr t') ke) m
| evcastptr_int_step: forall v (t: type) (m:smem) (ke:exprcont),
                   estep [Vptr v] (kecast Tint32 (Tptr t) ke) m [Vint32 (ptr_to_int32 v)] ke m

| evderef_step : forall (genv lenv:env) (M:mem) (a:addrval) (v:val) (t:type) 
                        (m:smem) (ke:exprcont),
                   m= (genv, lenv, M) -> load t M (addrval_to_addr a) =Some v -> 
                   estep [Vptr a] (kederef t ke) m  [v] ke m
| evoff_step : forall (b:block) (i i':int32) (ke:exprcont) (m:smem),
                 estep [Vptr (b, i)] (keoffset i' ke) m 
                       [Vptr (b, (Int.add i i'))] ke m
| evaddrelem_step : forall (v:val) (e:expr) (t:type) (ke:exprcont) (m:smem),
                      estep [v] (kearrbase e t ke) m (cure e) (kearrindex v t ke) m
| evaddrv_step: forall (v:val) (b:block) (i i' i'':int32)
                       (t:type) (ke:exprcont) (m:smem),
                  v = Vint32 i'' -> i'= Int.repr (Z_of_nat (typelen t)) ->
                  estep  [v] (kearrindex (Vptr (b, i)) t ke) m
                         [Vptr ( b, (Int.add i (Int.mul i' i'')))] ke m
| evuop_step : forall (op1:uop) (v v':val) (ke:exprcont) (m:smem) (t:type),
                 uop_eval v op1 = Some v' -> 
                 estep [v] (keop1 op1 t ke) m [v'] ke m
| evbop1_step : forall (op2:bop) (e:expr) (v:val) (t1 t2:type) (ke:exprcont) (m:smem),
                  estep [v] (keop2r op2 e t1 t2 ke) m
                        (cure e) (keop2l op2 v t1 t2 ke) m
| evbop2_step : forall (op2:bop) (v v' v'':val) (t1 t2 :type) (ke:exprcont) (m:smem),
                  bop_eval v' v t1 t2 op2=Some v'' -> 
                  estep [v] (keop2l op2 v' t1 t2 ke) m  [v'']  ke m.


Inductive estepstar :  cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop:=
| e_step0 : forall c ke m, estepstar c ke m c ke m
| e_stepn : forall c ke m c' ke' m' c'' ke'' m'', estep c ke m c' ke' m'-> 
                                                  estepstar c' ke' m' c'' ke'' m'' -> 
                                                  estepstar c ke m c'' ke'' m''.

Definition getfunrettype (fn : function) := match fn with
                                              | (t, _ ,_,_) => t
                                            end.


Inductive sstep: progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> Prop :=
(*Assign Steps*)
| sassign_step: forall (e1 e2:expr) (t1 t2:type) (ks:stmtcont) (m:smem) (p:progunit),
                  evaltype e1 m =Some t1 -> 
                  evaltype e2 m=Some t2 -> 
                  assign_type_match t1 t2 ->
                  sstep p (curs (sassign e1 e2)) ks m (cure e2) (kassignr e1 t1 ks) m

| sassignrv_step : forall (m:smem) (p:progunit) (v:val) (e:expr) (t:type) (ks:stmtcont),
                     sstep p [v] (kassignr e t ks) m 
                           (cure (eaddrof e))(kassignl v t ks) m

| sassignend_step : forall (m m':smem) (ge le :env) (M M':mem) (a:addrval) (v:val) 
                           (p:progunit) (ks:stmtcont) (t:type),
                      m= (ge, le, M) -> 
                      m'= ( ge, le, M') ->
                      store t M (addrval_to_addr a) v =Some M' ->
                      sstep p [Vptr a] (kassignl v t ks) m (curs (sskip None)) ks m' 

(*Function call Steps*)
| scalle_step: forall (p:progunit) (e:expr) (t:type) (m:smem) 
                      (f:fid) (ks:stmtcont) (el:exprlist),
                 evaltype e m =Some t ->
                 sstep p (curs (scalle e f el)) ks m (curs (scall f el))(kassignr e t ks) m

| spcall_step : forall (p:progunit) (t:type) (e:expr) (el:exprlist)
                       (m:smem) (ks:stmtcont) (f:fid), 
                  evaltype e m =Some t ->
                  sstep p (curs (scall f (cons e el))) ks m 
                        (cure e) (kfuneval f nil (t::nil) el ks) m

| snpcall_step : forall (m:smem)(f:fid) (p:progunit) (ks: stmtcont),
                   sstep p (curs (scall f nil)) ks m (curs (sfexec f nil nil)) ks m

| svfeval_step: forall (p:progunit) (v:val) (e:expr) (vl:vallist)
                       (el:exprlist) (ks:stmtcont) (m:smem) (f:fid) (tl:typelist) (t:type),
                  evaltype e m = Some t -> 
                  sstep p  [v] (kfuneval f vl tl (cons e el) ks) m 
                        (cure e) (kfuneval f (cons v vl) (t::tl) el ks) m
| svfevalnil_step: forall (p:progunit) (v:val) (vl:vallist) 
                          (ks:stmtcont) (m:smem) (f:fid) tl,
                     sstep p [v] (kfuneval f vl tl nil ks) m 
                           (curs (sfexec f (cons v vl ) tl)) ks m

| sfexec_step : forall (m m' :smem) (ge le:env) (M:mem) (p:progunit)
                       (t:type)(d1 d2:decllist)
                       (s:stmts) (ks:stmtcont) (vl:vallist) (f:fid) tl,
                  m=(ge, le, M) -> 
                  m'=  (ge, emp, M) -> 
                  p f=Some (t, d1, d2, s)->  
                  tlmatch (List.rev tl) d1  -> 
                  tl_vl_match tl vl = true ->
                  sstep p (curs (sfexec f vl tl)) ks m 
                        (curs (salloc vl (revlcons d1 d2))) 
                        (kcall f  s le ks) m'

| sallocp_step : forall (m m':smem) (ge le le':env) (M M' M'':mem)
                        (b:block) (v:val) (p:progunit) 
                        (vl:vallist) (dl:decllist) (ks:stmtcont) (x:var) (t:type),
                   m= (ge, le, M) -> 
                   m' = ( ge, le', M'') ->
                   alloc x t le M le' M' -> 
                   get le' x = Some (b,t)-> 
                   store t M'  (b, 0%Z) v = Some M''->
                   sstep p (curs (salloc  (cons v vl) (dcons x t dl))) ks m 
                         (curs (salloc  vl dl)) ks m'

| salloclv_step : forall (m m':smem) (ge le le':env) (M M':mem)
                         (t:type) (x:var) (p:progunit)
                         (dl:decllist) (ks:stmtcont),
                    m =  (ge, le, M) -> 
                    m' = (ge,le', M') ->
                    alloc x t le M le' M' ->
                    sstep p (curs (salloc  nil (dcons x t dl))) ks m
                          (curs (salloc  nil dl)) ks m'

| sallocend_step: forall (p:progunit) (f :fid) 
                         (s:stmts) (ks:stmtcont) (m:smem) (E:env),
                    sstep p (curs (salloc  nil dnil)) (kcall f s E ks) m 
                          (curs s) (kcall f s  E ks) m

| sret_step: forall (p:progunit) (m:smem)(M:mem) (ge le le':env)(f :fid)
                    (ks ks':stmtcont)  (al:freelist) (s: stmts),
               m=(ge, le, M) -> 
               callcont ks =Some (kcall f s le' ks') ->
               getaddr le = al ->
               sstep p (curs sret) ks m (curs (sfree al None)) ks m


| srete_step : forall (p:progunit) (ks:stmtcont)  
                      (e:expr) (m:smem),
                 sstep p (curs (srete e)) ks m (cure e) (kret ks) m

| sretv_step: forall (p:progunit) (m:smem) (le ge:env)
                     (M:mem) (ks:stmtcont) (f:fid)  
                     (al:freelist) (v:val)(s : stmts) ,
                m=(ge, le, M) ->
                callcont ks <> None -> 
                getaddr le = al->
                sstep p [v] (kret ks) m (curs (sfree al (Some v))) ks m 

| sfree_step : forall (m m':smem) (le ge :env) (M M':mem) (b:block) (t:type) (p:progunit) 
                      (al:freelist) (ks:stmtcont) (v:option val),
                 m=(ge, le, M) -> 
                 m' = (ge, le , M') -> 
                 free t b M =Some M' -> 
                 sstep p (curs (sfree (cons (pair b t) al) v)) ks m 
                       (curs (sfree al v)) ks m'

| sfreeend_step : forall (p:progunit) (ks ks':stmtcont) (m m':smem)
                         (ge le le':env) (M:mem) (s : stmts)(f:fid) (v:option val),
                    m= (ge, le, M) -> 
                    m' = (ge, le', M) -> 
                    callcont ks =Some (kcall f  s le' ks') ->
                    sstep p (curs (sfree nil v)) ks m (curs (sskip v)) ks' m'
(*

| sfreev_step : forall (m m':smem) (le ge :env) (M M':mem) (b:block) (t:type) (p:progunit) 
                     (al:freelist) (ks:stmtcont) (v:val),
                m=(ge, le, M) -> 
                m'= ( ge, le, M') -> 
                free t b M =Some M' -> 
                sstep p (curs (sfreev (cons (pair (b, 0%Z) t) al) v)) ks m 
                                  (curs (sfreev al v)) ks m'

 
| sfreevend_step : forall (p:progunit) (ks ks':stmtcont) (f:fid) (t: type)
                  (m m':smem) (v:val)(M:mem) (ge le le':env)(s : stmts),
                   m=( ge, le, M) -> 
                   m'= ( ge, le', M) -> 
                   t <> Tvoid -> 
                   callcont ks =Some (kcall f t s le' ks') ->
                   sstep p (curs (sfreev nil v)) ks m (curv v) ks' m'
 *)

(*Sequential Step*)                   
| sseq_step : forall (s1 s2:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                sstep p (curs (sseq s1 s2)) ks m (curs s1) (kseq s2 ks) m

| svseq_step : forall (p:progunit) (v:val) (s:stmts) (ks:stmtcont) (m:smem),
                 sstep p [v] (kseq s ks) m (curs s) ks m

| sskip_step : forall (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                 sstep p SKIP (kseq s ks) m (curs s) ks m


(*If then else Step*)
| sif_step : forall (e:expr) (s1 s2 :stmts) (ks:stmtcont) (m:smem) (p:progunit),
               sstep p (curs (sif e s1 s2)) ks m (cure e) (kif s1 s2 ks) m

| sifthen_step: forall  (e:expr) (s :stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (sifthen e s)) ks m (cure e) (kif s (sskip None) ks) m

| svift_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some true ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s1) ks m
| sviff_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some false ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s2) ks m

(*While Step*)

| swhile_step : forall (e:expr) (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (swhile e s)) ks m (cure e) (kwhile e s ks) m


| svwhilet_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some true ->
                   sstep p  (curs (sskip (Some v))) (kwhile e s ks) m (curs s) (kseq (swhile e s) ks) m

| svwhilef_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some false ->
                   sstep p (curs (sskip (Some v))) (kwhile e s ks) m SKIP ks m.



Inductive sstepev : progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> val -> Prop:=
|sprint_step: forall (e:expr) (v:val) (m:smem) (ks:stmtcont) (s:stmts) (p:progunit),
                evalval e m = Some v -> sstepev p (curs (sprint e)) ks m SKIP ks m v.


Inductive cstep: progunit -> code -> smem -> code -> smem -> Prop :=
| expr_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ke ke':exprcont) (ks:stmtcont),
                C = ( c, ( ke, ks)) -> 
                estep c ke m c' ke' m' ->
                cstep p C m (c', ( ke', ks)) m'
| stmt_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ks ks':stmtcont),
                C = (c, (kenil, ks)) -> 
                sstep p c ks m c' ks' m' ->
                cstep p C m (c', (kenil , ks')) m'.

Inductive cstepev : progunit-> code -> smem -> code -> smem -> val-> Prop :=
| stmt_stepev :  forall (expr_step p p:progunit) (C:code) (m:smem) (c c':cureval)
                        (ks ks':stmtcont) (v:val),
                   C = (c, (kenil, ks)) -> 
                   sstepev p c ks m c' ks' m v ->
                   cstepev p C m (c', (kenil, ks')) m v. 

Inductive cstepstar: progunit -> code -> smem -> code -> smem -> Prop :=
| c_stepstar0: forall (p:progunit) (C:code) (m:smem),
                 cstepstar p C m C m
| c_stepstarn: forall (p:progunit) (C C' C'':code) (m m' m'':smem),
                 cstep p C m C' m' -> cstepstar p C' m' C'' m''->
                 cstepstar p C m C'' m''.

Definition cstepabt (p:progunit) (C:code) (m:smem) := 
  ~ (exists C' m' ev, cstep p C m C' m' \/ cstepev p C m C' m' ev).


Definition pumerge (p1 p2:progunit):=
  fun (f:fid) => match p1 f with 
                   | Some fc => Some fc 
                   | None => match p2 f with 
                               | Some fc => Some fc
                               | None => None
                             end
                 end.

Open Scope Z_scope.
Definition is_length (si:is):=
  match (length si) with
    | 1%nat => Vint32 Int.one
    | _ => Vint32 Int.zero
  end.

Definition intStart : nat := Z.to_nat 15.
Definition intStartInt : int := Int.repr 15.
Definition intEndInt : int := Int.repr 3.
Definition base1 : int := Int.repr 1.


Fixpoint getLevel (er : ier) (x : hid) (level : int) (levelInt : int): int :=
  match x with
  | S x' => if (er x) && (Int.ltu intEndInt levelInt) then getLevel er x' (Int.or level (Int.shl base1 levelInt)) (Int.sub levelInt base1)
                      else getLevel er x' level (Int.sub levelInt base1)
  | O => level
  end.

(*-----------------------------------------content about MPAX-------------------------------------------*)

Definition xmc_xmpaxh: ident := 3000%Z.
Definition mpaxh_bAddr: ident := 3001%Z.
Definition mpaxh_segSize: ident := 3002%Z.
Definition xmc_xmpaxl: ident := 3003%Z.
Definition mpaxl_rAddr: ident := 3004%Z.
Definition mpaxl_sr: ident := 3005%Z.
Definition mpaxl_sw: ident := 3006%Z.
Definition mpaxl_sx: ident := 3007%Z.
Definition mpaxl_ur: ident := 3008%Z.
Definition mpaxl_uw: ident := 3009%Z.
Definition mpaxl_ux: ident := 3010%Z.
Definition msmc_sesmpaxh: ident := 3011%Z.
Definition sesmpaxh_bAddr: ident := 3012%Z.
Definition sesmpaxh_segSz: ident := 3013%Z.
Definition msmc_sesmpaxl: ident := 3014%Z.
Definition sesmpaxl_raddr: ident := 3015%Z.
Definition sesmpaxl_sr: ident := 3016%Z.
Definition sesmpaxl_sw: ident := 3017%Z.
Definition sesmpaxl_sx: ident := 3018%Z.
Definition sesmpaxl_ur: ident := 3019%Z.
Definition sesmpaxl_uw: ident := 3020%Z.
Definition sesmpaxl_ux: ident := 3021%Z.
Definition msmc_smsmpaxh: ident := 3022%Z.
Definition smsmpaxh_bAddr: ident := 3023%Z.
Definition smsmpaxh_segSz: ident := 3024%Z.
Definition msmc_smsmpaxl: ident := 3025%Z.
Definition smsmpaxl_raddr: ident := 3026%Z.
Definition smsmpaxl_sr: ident := 3027%Z.
Definition smsmpaxl_sw: ident := 3028%Z.
Definition smsmpaxl_sx: ident := 3029%Z.
Definition smsmpaxl_ur: ident := 3030%Z.
Definition smsmpaxl_uw: ident := 3031%Z.
Definition smsmpaxl_ux: ident := 3032%Z.

Notation " 'XMC_XMPAXL' " := (Tstruct xmc_xmpaxl 
                                                     (dcons mpaxl_rAddr Tint32
                                                           (dcons mpaxl_sr Tint8
                                                               (dcons mpaxl_sw Tint8 
                                                                  (dcons mpaxl_sx Tint8 
                                                                      (dcons mpaxl_ur Tint8 
                                                                          (dcons mpaxl_uw Tint8 
                                                                              (dcons mpaxl_ux Tint8 dnil)))))))) (at level 5).

Notation " 'XMC_XMPAXH' " := (Tstruct xmc_xmpaxh 
                                                     (dcons mpaxh_bAddr Tint32
                                                           (dcons mpaxh_segSize Tint8 dnil))) (at level 5).

Notation " 'MSMC_SMSMPAXL' " := (Tstruct msmc_smsmpaxl 
                                                     (dcons smsmpaxl_raddr Tint32
                                                           (dcons smsmpaxl_sr Tint8
                                                               (dcons smsmpaxl_sw Tint8 
                                                                  (dcons smsmpaxl_sx Tint8 
                                                                      (dcons smsmpaxl_ur Tint8 
                                                                          (dcons smsmpaxl_uw Tint8 
                                                                              (dcons smsmpaxl_ux Tint8 dnil)))))))) (at level 5).

Notation " 'MSMC_SMSMPAXH' " := (Tstruct msmc_smsmpaxh 
                                                     (dcons smsmpaxh_bAddr Tint32
                                                           (dcons smsmpaxh_segSz Tint8 dnil))) (at level 5).

Notation " 'MSMC_SESMPAXL' " := (Tstruct msmc_sesmpaxl 
                                                     (dcons sesmpaxl_raddr Tint32
                                                           (dcons sesmpaxl_sr Tint8
                                                               (dcons sesmpaxl_sw Tint8 
                                                                  (dcons sesmpaxl_sx Tint8 
                                                                      (dcons sesmpaxl_ur Tint8 
                                                                          (dcons sesmpaxl_uw Tint8 
                                                                              (dcons sesmpaxl_ux Tint8 dnil)))))))) (at level 5).

Notation " 'MSMC_SESMPAXH' " := (Tstruct msmc_sesmpaxh 
                                                     (dcons sesmpaxh_bAddr Tint32
                                                           (dcons sesmpaxh_segSz Tint8 dnil))) (at level 5).

Inductive mpax_tpid :=
| smsl_raddr: mpax_tpid
| smsl_sr: mpax_tpid
| smsl_sw: mpax_tpid
| smsl_sx: mpax_tpid
| smsl_ur: mpax_tpid
| smsl_uw: mpax_tpid
| smsl_ux: mpax_tpid
| smsh_baddr: mpax_tpid
| smsh_segsize: mpax_tpid
| sesl_raddr: mpax_tpid
| sesl_sr: mpax_tpid
| sesl_sw: mpax_tpid
| sesl_sx: mpax_tpid
| sesl_ur: mpax_tpid
| sesl_uw: mpax_tpid
| sesl_ux: mpax_tpid
| sesh_baddr: mpax_tpid
| sesh_segsize: mpax_tpid
| xmc_raddr: mpax_tpid
| xmc_sr: mpax_tpid
| xmc_sw: mpax_tpid
| xmc_sx: mpax_tpid
| xmc_ur: mpax_tpid
| xmc_uw: mpax_tpid
| xmc_ux: mpax_tpid
| xmc_baddr: mpax_tpid
| xmc_segsize: mpax_tpid
.

Definition clearl (v : int) (leftl : nat) :=
  Int.repr ((Int.unsigned (Int.shl v (Int.repr (Z.of_nat leftl)))) / (two_power_nat leftl)).

Definition clearr (v : int) (rightl : nat) :=
  Int.shru v (Int.repr (Z.of_nat rightl)).

Definition get_part (v : int) (leftl : nat) (rightl : nat) :=
  clearr (clearl v leftl) rightl.

Definition clear_part (v : int) (leftl : nat) (rightl : nat) :=
Int.xor v (Int.shl (get_part v leftl rightl) (Int.repr (Z.of_nat rightl))).

Definition set_part (v : int) (leftl : nat) (rightl : nat) (v': int) :=
Int.or (clear_part v leftl rightl) (Int.shl v' (Int.repr (Z.of_nat rightl))).

Definition get_mpax (v: int) (id : mpax_tpid) :=
match id with
| smsl_raddr => get_part v 0 8
| smsl_sr => get_part v 26 5
| smsl_sw => get_part v 27 4
| smsl_sx => get_part v 28 3
| smsl_ur => get_part v 29 2
| smsl_uw => get_part v 30 1
| smsl_ux => get_part v 31 0
| smsh_baddr => get_part v 0 12
| smsh_segsize => get_part v 20 0
| sesl_raddr => get_part v 0 8
| sesl_sr => get_part v 26 5
| sesl_sw => get_part v 27 4
| sesl_sx => get_part v 28 3
| sesl_ur => get_part v 29 2
| sesl_uw => get_part v 30 1
| sesl_ux => get_part v 31 0
| sesh_baddr => get_part v 0 12
| sesh_segsize => get_part v 20 0
| xmc_raddr => get_part v 0 8
| xmc_sr => get_part v 26 5
| xmc_sw => get_part v 27 4
| xmc_sx => get_part v 28 3
| xmc_ur => get_part v 29 2
| xmc_uw => get_part v 30 1
| xmc_ux => get_part v 31 0
| xmc_baddr => get_part v 0 12
| xmc_segsize => get_part v 20 0
end.

Definition set_mpax (v: int) (id : mpax_tpid) (v' : int) :=
match id with
| smsl_raddr => set_part v 0 8 v'
| smsl_sr => set_part v 26 5 v'
| smsl_sw => set_part v 27 4 v'
| smsl_sx => set_part v 28 3 v'
| smsl_ur => set_part v 29 2 v'
| smsl_uw => set_part v 30 1 v'
| smsl_ux => set_part v 31 0 v'
| smsh_baddr => set_part v 0 12 v'
| smsh_segsize => set_part v 20 0 v'
| sesl_raddr => set_part v 0 8 v'
| sesl_sr => set_part v 26 5 v'
| sesl_sw => set_part v 27 4 v'
| sesl_sx => set_part v 28 3 v'
| sesl_ur => set_part v 29 2 v'
| sesl_uw => set_part v 30 1 v'
| sesl_ux => set_part v 31 0 v'
| sesh_baddr => set_part v 0 12 v'
| sesh_segsize => set_part v 20 0 v'
| xmc_raddr => set_part v 0 8 v'
| xmc_sr => set_part v 26 5 v'
| xmc_sw => set_part v 27 4 v'
| xmc_sx => set_part v 28 3 v'
| xmc_ur => set_part v 29 2 v'
| xmc_uw => set_part v 30 1 v'
| xmc_ux => set_part v 31 0 v'
| xmc_baddr => set_part v 0 12 v'
| xmc_segsize => set_part v 20 0 v'
end.

Fixpoint set_mpax_struct (v : int32) (t : list mpax_tpid) (vl : list val) : int32 :=
  match t with
  | nil => v
  | tpid :: t' => match vl with
                  | Vint32 vt :: vl' => set_mpax (set_mpax_struct v t' vl') tpid vt
                  | _ => v
                  end
  end.

Fixpoint get_mpax_struct (v: int32) (t : list mpax_tpid) : list val :=
    match t with
    | nil => nil
    | tpid :: t' => (Vint32 (get_mpax v tpid)) :: get_mpax_struct v t'
    end.

(* copy from assertion.v *)

Definition ptomval (l : addr) (b:bool) (v : memval) (M : mem) := M = sig l (b,v).

Fixpoint  ptomvallist (l : addr) (b1: bool) ( vl : mvallist)  (M: mem) {struct vl} : Prop :=
   match  vl, l with
   | nil, _  => M = emp
   | u :: vl', (b, i) =>
     exists M1 M2, join M1 M2 M /\ 
                   ptomval l b1 u M1 /\ ptomvallist (b, (Z.add i  1%Z)) b1 vl' M2
   end.

Definition mapstoval (l : addr) (t : type) (b: bool) (v : val)  (m : mem) := 
  exists vl, encode_val t v = vl /\ (ptomvallist l b vl m).

Fixpoint id_nth' id decl n:=
  match decl with
    | dnil => None
    | dcons id' t decl'=> match Zbool.Zeq_bool id id' with
                            | true => Some n
                            | false => id_nth' id decl' (S n)
                          end
  end. 

Definition id_nth id decl := id_nth' id decl 0.

Fixpoint update_nth_val (n : nat) (vl : vallist) (v : val){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0%nat => v::vl'
                  | S n' => v'::(update_nth_val n' vl' v)
                end
  end.

(* copy from evt_spec_defs.v *)
Fixpoint Get_struct (l: (list (addrval * type * (list val))))(a: addrval) :  (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_struct l' a 
                                   end  
end.

Fixpoint Set_struct' (l: (list (addrval * type * (list val))))(a: addrval) (id : ident ) (b: val)
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

Fixpoint Set_struct (l: (list (addrval * type * (list val))))(a: addrval) (t' : type) (vl': list val)
     :  (list (addrval * type * (list val))) :=
  match l with
  | nil => nil
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                  | true => match (type_eq t t') with
                                                     | true => (ad, t, vl') :: l'
                                                     | false => (ad, t, vl) :: (Set_struct l' a t' vl')
                                                end
                                  | false => (ad, t, vl) :: (Set_struct l' a t' vl')
                               end
  end.

(*--------------------------------------------end of MPAX-------------------------------------------------*)


Inductive loststep: progunit -> code -> taskst -> code -> taskst -> Prop:=
| ostc_step: forall (C C':code) (m m':smem) (i:isr) (er:ier) (au:localst) (p:progunit),
               cstep p C m C' m'
               -> loststep p C (m , i, er, au) C' ( m', i, er, au)

| exint_step: forall (C:code) (ks ks':stmtcont) (c:cureval) (ke:exprcont)  
                     (ir:isr) (er:ier) (ei:ie) (si:is) (ci:cs) (i:hid) (p:progunit) ge le m le',
                C =(curs (sprim exint), (kenil, ks)) -> 
                intcont ks = Some (kint c ke le' ks') ->
                loststep p C ((ge,le,m), ir, er, ( ei, (cons i si), ci)) 
                         (c, ( ke, ks')) ((ge,le',m),ir,er,(true, si, ci))

| eoi_step:  forall (C:code) (ks:stmtcont) (m:smem)  (au:localst)
                    (ir:isr) (er:ier) ( id: hid)  (p:progunit) (i:int32),
               C =((curs (sprim (eoi i))), (kenil, ks)) ->
               id = (Z.to_nat (Int.unsigned i))  -> 0 <= Int.unsigned i < Z_of_nat INUM->
               loststep p C (m, ir, er, au) 
                        (SKIP, (kenil, ks)) 
                        (m , (isrupd ir id false) , er, au)
| eoint_step:  forall (C:code) (ks:stmtcont) (m:smem)  (au:localst)
                    (ir:isr) (er:ier) ( id: hid)  (p:progunit) (i:int32) G E M b vi,
                  C =((curs (sprim (eoint vi))), (kenil, ks)) ->
                  m=(G,E,M) -> 
                  get G vi = Some (b,Tint32) -> 
                  load Tint32 M (b,0%Z) = Some (Vint32 i) ->
                  id = (Z.to_nat (Int.unsigned i))  -> 0 <= Int.unsigned i < Z_of_nat INUM ->
                  loststep p C (m, ir, er, au) 
                            (SKIP, (kenil, ks)) 
                            (m , (isrupd ir id false) , er, au)
| cli_step : forall (C:code) (ks:stmtcont) (m:smem)
                    (ir:isr) (er:ier) (ei:ie) (si:is) (ci:cs) (p:progunit),
               C = ((curs (sprim cli)), (kenil, ks)) -> 
               loststep p C (m, ir, er, (ei, si, ci)) 
                        (SKIP, (kenil, ks)) 
                        (m, ir, er, (false, si, ci))

| sti_step : forall (C:code) (ks:stmtcont) (m:smem)
                    (ir:isr) (er:ier) (ei:ie) (si:is) (ci:cs) (p:progunit),
               C =((curs (sprim sti)), (kenil, ks)) -> 
               loststep p C (m, ir, er, (ei, si, ci)) 
                        (SKIP, (kenil, ks)) 
                        (m, ir, er, (true, si, ci))

| encrit_step : forall (C:code) (ks:stmtcont) (m:smem)
                       (ir:isr) (er:ier) (ei:ie) (si:is) (ci:cs)  (p:progunit),
                  C =((curs (sprim encrit)), (kenil, ks)) -> 
                  loststep p C (m , ir, er,  (ei,  si, ci)) 
                           (SKIP, (kenil, ks)) 
                           (m,  ir , er, (false, si, (cons ei ci)))

| excrit_step : forall (C:code) (ks:stmtcont) (m:smem)
                       (ir:isr) (er:ier) (ei ei':ie) (si:is) (ci:cs)(p:progunit),
                  C =((curs (sprim excrit)), (kenil, ks)) -> 
                  loststep p C ( m ,ir, er, (ei,  si, (cons ei' ci))) 
                           (SKIP, (kenil,  ks)) 
                           ( m,ir, er, (ei',  si, ci))
| checkis_step : forall  (C:code) (ks:stmtcont) (m:smem)
                         (ir:isr) (er:ier) (ei ei':ie) (si:is) (ci:cs) (x:var) (p:progunit) G E M M' m' b x,
                   C =((curs (sprim (checkis x))), (kenil, ks)) ->
                   m=(G,E,M) ->
                   get E x = Some (b,Tint32) ->
                   store Tint32 M (b,0%Z) (is_length si) = Some M'->
                   m'= (G,E,M') ->
                   loststep p C ( m ,ir, er, (ei,  si, ci)) 
                            (SKIP, (kenil,  ks)) 
                            ( m',ir, er, (ei,  si, ci))
(*| dintp_step : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                      (ir:isr) (er:ier) (irqLine:var) (p:progunit),
                   C =((curs (sprim (dintp irqLine))), (kenil, ks)) ->
                   loststep p C (m, ir, er, au)
                                (SKIP, (kenil,  ks))
                                (m, ir, (ierupd er (Z.to_nat irqLine) false), au)*)
| dintp_stepp : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                                (ir:isr) (er:ier) (irqLine:var) (p:progunit) G E M b x,
                             C =((curs (sprim (dintp irqLine))), (kenil, ks)) ->
                             m=(G,E,M) -> 
                             get E irqLine = Some (b,Tint32) -> 
                             load Tint32 M (b,0%Z) = Some (Vint32 x) ->
                             loststep p C (m, ir, er, au)
                                          (SKIP, (kenil,  ks))
                                          (m, ir, (ierupd er (Z.to_nat (Int.unsigned x)) false), au)             
(*| rintp_step : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                      (ir:isr) (er:ier) (irqLine:var) (p:progunit),
                   C =((curs (sprim (rintp irqLine))), (kenil, ks)) ->
                   loststep p C (m, ir, er, au)
                                (SKIP, (kenil,  ks))
                                (m, ir, (ierupd er (Z.to_nat irqLine) true), au)*)
| rintp_stepp : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                                (ir:isr) (er:ier) (irqLine:var) (p:progunit) G E M b x,
                             C =((curs (sprim (rintp irqLine))), (kenil, ks)) ->
                             m=(G,E,M) -> 
                             get E irqLine = Some (b,Tint32) -> 
                             load Tint32 M (b,0%Z) = Some (Vint32 x) ->
                             loststep p C (m, ir, er, au)
                                          (SKIP, (kenil,  ks))
                                          (m, ir, (ierupd er (Z.to_nat (Int.unsigned x)) true), au)
| dint_step : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                     (ir:isr) (er:ier) (level:var) (p:progunit) G E M M' m' b level,
                   C =((curs (sprim (dint level))), (kenil, ks)) ->
                   m=(G,E,M) ->
                   get E level = Some (b,Tint32) ->
                   store Tint32 M (b,0%Z) (Vint32 (getLevel er intStart (Int.repr 0) intStartInt)) = Some M'->
                   m'= (G,E,M') ->
                   loststep p C (m, ir, er, au)
                                (SKIP, (kenil,  ks))
                                (m', ir, empupd er, au)
(*| rint_step : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                     (ir:isr) (er:ier) (level:var) (p:progunit),
                   C =((curs (sprim (rint level))), (kenil, ks)) -> 
                   loststep p C (m, ir, er, au)
                                (SKIP, (kenil,  ks))
                                (m, ir, (ierupds er level), au)*)
| rint_stepp : forall (C:code) (ks:stmtcont) (m:smem) (au:localst)
                                (ir:isr) (er:ier) (level:var) (p:progunit)  G E M b x,
                              C =((curs (sprim (rint level))), (kenil, ks)) -> 
                              m=(G,E,M) -> 
                              get E level = Some (b,Tint32) -> 
                              load Tint32 M (b,0%Z) = Some (Vint32 x) ->
                              loststep p C (m, ir, er, au)
                                           (SKIP, (kenil,  ks))
                                           (m, ir, (ierupds_int er x), au)
| generateipc_step:  forall (C:code) (ks:stmtcont) (u: taskst) (e1 e2: expr) v1 v2(p:progunit),
                  C =((curs (sprim (sgenerateipc e1 e2))), (kenil, ks)) ->
                  evaltype e1 (get_smem u) = Some Tint8 ->
                  evaltype e2 (get_smem u) = Some Tint32 ->
                  evalval e1 (get_smem u) = Some v1 ->
                  evalval e2 (get_smem u) = Some v2 ->
                  v1 <> Vundef ->
                  v2 <> Vundef ->
                  loststep p C u (SKIP, (kenil, ks)) u
| getsem_step:  forall (C:code) (ks:stmtcont) (u: taskst) (e: expr)  v  (p:progunit),
                  C =((curs (sprim (sgetsem e))), (kenil, ks)) ->
                  evaltype e (get_smem u) = Some Tint8 ->
                  evalval e (get_smem u) = Some v ->
                  v <> Vundef ->
                  loststep p C u (SKIP, (kenil, ks)) u
| postsem_step:  forall (C:code) (ks:stmtcont) (u: taskst) (e: expr)  v (p:progunit),
                  C =((curs (sprim (spostsem e))), (kenil, ks)) ->
                  evaltype e (get_smem u) = Some Tint8 ->
                  evalval e (get_smem u) = Some v ->
                  v <> Vundef ->
                  loststep p C u (SKIP, (kenil, ks)) u
| clearipc_step:  forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2: expr) (p:progunit) v1 v2 G E M M' lst,
                  C =((curs (sprim (sclearipc e1 e2))), (kenil, ks)) ->
                  m = (G,E,M) ->
                  evaltype e1 m = Some Tint8 ->
                  evaltype e2 m = Some Tint32 ->
                  evalval e1 m = Some v1 ->
                  evalval e2 m = Some v2 ->
                   v1 <> Vundef ->
                   v2 <> Vundef ->
                  store Tint32 M (addrval_to_addr ipcgr_addr)  (Vint32 Int.zero) = Some M'->
                  m' = (G,E,M') ->
                  loststep p C (m,ir, er, lst)  (SKIP, (kenil, ks)) (m',ir, er, lst) 
| cslsemaccdir_step:  forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2: expr) (p:progunit) v1 a G E M M' lst,
                  forall (x:var) v2, 
                  C =((curs (sprim (scsl_semaccdir e1 e2))), (kenil, ks)) ->
                  m = (G,E,M) ->
                  evaltype e1 m = Some Tint8 ->
                  evaltype e2 m = Some Tint8 ->
                  evalval e1 m = Some v1 ->
                  e2 = evar x -> 
                  evalval (eaddrof e2) m = Some (Vptr a) ->
                  v1 <> Vundef ->
                  (v2 = Vint32 Int.zero \/ v2 = Vint32 Int.one) ->
                  store Tint8 M (addrval_to_addr a) v2 =Some M' ->
                  m' = (G,E,M') ->
                  loststep p C (m,ir, er, lst)  (SKIP, (kenil, ks)) (m',ir, er, lst)
| cslsemrel_step:  forall (C:code) (ks:stmtcont) (u: taskst) (e: expr)  v (p:progunit),
                  C =((curs (sprim (scsl_semrel e))), (kenil, ks)) ->
                  evaltype e (get_smem u) = Some Tint8 ->
                  evalval e (get_smem u) = Some v ->
                  v <> Vundef ->
                  loststep p C u (SKIP, (kenil, ks)) u

| csl_msmc_getSMSMPAXL_step:
                 forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                        (p:progunit) v1 v2 v3 G E M M1 M2 M3 M4 M5 M6 M7
                        M1' M2' M3' M4' M5' M6' M7' mx M'
                        mx1 mx2 mx3 mx4 mx5 mx6 mx1' mx2' mx3' mx4' mx5' mx6'
                         lst b x y z0 z1 z2 z3 z4 z5 z6,
                  C =((curs (sprim (scsl_msmc_getSMSMPAXL e1 e2 e3))), (kenil, ks)) ->
                  m = (G,E,M) ->
                  evaltype e1 m = Some Tint32 ->
                  evaltype e2 m = Some Tint32 ->
                  evaltype e3 m = Some (Tptr MSMC_SMSMPAXL) ->
                  evalval e1 m = Some v1 ->
                  evalval e2 m = Some (Vint32 v2) ->
                  evalval e3 m = Some (Vptr v3) ->
                  v1 <> Vundef ->
                  Vint32 v2 <> Vundef ->
                  Vptr v3 <> Vundef ->
                  v3 = (b,y) -> 
                  load Tint32 M (sms_mpax_block,((Int.unsigned v2)*8)%Z) = Some (Vint32 x) ->
                  mapstoval (b, ((Int.unsigned y) + 0)%Z) Tint32 true (Vint32 z0) M1 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 4)))) Tint8 true (Vint32 z1) M2 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 5)))) Tint8 true (Vint32 z2) M3 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 6)))) Tint8 true (Vint32 z3) M4 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 7)))) Tint8 true (Vint32 z4) M5 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 8)))) Tint8 true (Vint32 z5) M6 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 9)))) Tint8 true (Vint32 z6) M7 ->
                  join M2 M1 mx1 /\ join M3 mx1 mx2 /\ join M4 mx2 mx3 /\ join M5 mx3 mx4 /\
                  join M6 mx4 mx5 /\ join M7 mx5 mx6 /\ join mx6 mx M ->
                  store Tint32 M1 (b,((Int.unsigned y) + 0)%Z) (Vint32 (get_mpax x smsl_raddr)) = Some M1' ->
                  store Tint8 M2 (b,(Int.unsigned (Int.add y (Int.repr 4)))) (Vint32 (get_mpax x smsl_sr)) = Some M2' ->
                  store Tint8 M3 (b,(Int.unsigned (Int.add y (Int.repr 5)))) (Vint32 (get_mpax x smsl_sw)) = Some M3' ->
                  store Tint8 M4 (b,(Int.unsigned (Int.add y (Int.repr 6)))) (Vint32 (get_mpax x smsl_sx)) = Some M4' ->
                  store Tint8 M5 (b,(Int.unsigned (Int.add y (Int.repr 7)))) (Vint32 (get_mpax x smsl_ur)) = Some M5' ->
                  store Tint8 M6 (b,(Int.unsigned (Int.add y (Int.repr 8)))) (Vint32 (get_mpax x smsl_uw)) = Some M6' ->
                  store Tint8 M7 (b,(Int.unsigned (Int.add y (Int.repr 9)))) (Vint32 (get_mpax x smsl_ux)) = Some M7' ->
                  join M2' M1' mx1' /\ join M3' mx1' mx2' /\ join M4' mx2' mx3' /\ join M5' mx3' mx4' /\
                  join M6' mx4' mx5' /\ join M7' mx5' mx6' /\ join mx6' mx M' ->
                  m' = (G,E,M') ->
                  loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_msmc_setSMSMPAXL_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                                                           (p:progunit) v1 v2 v3 G E M M1 lst b x x' x1 x2 x3 x4 x5 x6 x7 y vl,
                 C =((curs (sprim (scsl_msmc_setSMSMPAXL e1 e2 e3))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some Tint32 ->
                 evaltype e3 m = Some (Tptr MSMC_SMSMPAXL) ->
                 evalval e1 m = Some v1 ->
                 evalval e2 m = Some (Vint32 v2) ->
                 evalval e3 m = Some (Vptr v3) ->
                 v1 <> Vundef ->
                 Vint32 v2 <> Vundef ->
                 Vptr v3 <> Vundef ->
                 load Tint32 M (sms_mpax_block,((Int.unsigned v2)*8)%Z) = Some (Vint32 x) ->
                 v3 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 5)))) = Some (Vint32 x3) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 6)))) = Some (Vint32 x4) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 7)))) = Some (Vint32 x5) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 8)))) = Some (Vint32 x6) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 9)))) = Some (Vint32 x7) ->
                 vl = (Vint32 x1 ::Vint32 x2 ::Vint32 x3 ::Vint32 x4 ::Vint32 x5 ::Vint32 x6 ::Vint32 x7 :: nil) ->
                 x' = set_mpax_struct x (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) vl ->
                 store Tint32 M (sms_mpax_block,((Int.unsigned v2)*8)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

  | csl_msmc_getSESMPAXL_step:
                 forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                        (p:progunit) v1 v2 v3 G E M M1 M2 M3 M4 M5 M6 M7
                        M1' M2' M3' M4' M5' M6' M7' mx M'
                        mx1 mx2 mx3 mx4 mx5 mx6 mx1' mx2' mx3' mx4' mx5' mx6'
                         lst b x y z0 z1 z2 z3 z4 z5 z6,
                  C =((curs (sprim (scsl_msmc_getSESMPAXL e1 e2 e3))), (kenil, ks)) ->
                  m = (G,E,M) ->
                  evaltype e1 m = Some Tint32 ->
                  evaltype e2 m = Some Tint32 ->
                  evaltype e3 m = Some (Tptr MSMC_SESMPAXL) ->
                  evalval e1 m = Some v1 ->
                  evalval e2 m = Some (Vint32 v2) ->
                  evalval e3 m = Some (Vptr v3) ->
                  v1 <> Vundef ->
                  Vint32 v2 <> Vundef ->
                  Vptr v3 <> Vundef ->
                  v3 = (b,y) -> 
                  load Tint32 M (ses_mpax_block,((Int.unsigned v2)*8)%Z) = Some (Vint32 x) ->
                  mapstoval (b, ((Int.unsigned y) + 0)%Z) Tint32 true (Vint32 z0) M1 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 4)))) Tint8 true (Vint32 z1) M2 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 5)))) Tint8 true (Vint32 z2) M3 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 6)))) Tint8 true (Vint32 z3) M4 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 7)))) Tint8 true (Vint32 z4) M5 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 8)))) Tint8 true (Vint32 z5) M6 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 9)))) Tint8 true (Vint32 z6) M7 ->
                  join M2 M1 mx1 /\ join M3 mx1 mx2 /\ join M4 mx2 mx3 /\ join M5 mx3 mx4 /\
                  join M6 mx4 mx5 /\ join M7 mx5 mx6 /\ join mx6 mx M ->
                  store Tint32 M1 (b,((Int.unsigned y) + 0)%Z) (Vint32 (get_mpax x sesl_raddr)) = Some M1' ->
                  store Tint8 M2 (b,(Int.unsigned (Int.add y (Int.repr 4)))) (Vint32 (get_mpax x sesl_sr)) = Some M2' ->
                  store Tint8 M3 (b,(Int.unsigned (Int.add y (Int.repr 5)))) (Vint32 (get_mpax x sesl_sw)) = Some M3' ->
                  store Tint8 M4 (b,(Int.unsigned (Int.add y (Int.repr 6)))) (Vint32 (get_mpax x sesl_sx)) = Some M4' ->
                  store Tint8 M5 (b,(Int.unsigned (Int.add y (Int.repr 7)))) (Vint32 (get_mpax x sesl_ur)) = Some M5' ->
                  store Tint8 M6 (b,(Int.unsigned (Int.add y (Int.repr 8)))) (Vint32 (get_mpax x sesl_uw)) = Some M6' ->
                  store Tint8 M7 (b,(Int.unsigned (Int.add y (Int.repr 9)))) (Vint32 (get_mpax x sesl_ux)) = Some M7' ->
                  join M2' M1' mx1' /\ join M3' mx1' mx2' /\ join M4' mx2' mx3' /\ join M5' mx3' mx4' /\
                  join M6' mx4' mx5' /\ join M7' mx5' mx6' /\ join mx6' mx M' ->
                  m' = (G,E,M') ->
                  loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_msmc_setSESMPAXL_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                                                           (p:progunit) v1 v2 v3 G E M M1 lst b x x' x1 x2 x3 x4 x5 x6 x7 y vl,
                 C =((curs (sprim (scsl_msmc_setSESMPAXL e1 e2 e3))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some Tint32 ->
                 evaltype e3 m = Some (Tptr MSMC_SESMPAXL) ->
                 evalval e1 m = Some v1 ->
                 evalval e2 m = Some (Vint32 v2) ->
                 evalval e3 m = Some (Vptr v3) ->
                 v1 <> Vundef ->
                 Vint32 v2 <> Vundef ->
                 Vptr v3 <> Vundef ->
                 load Tint32 M (ses_mpax_block,((Int.unsigned v2)*8)%Z) = Some (Vint32 x) ->
                 v3 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 5)))) = Some (Vint32 x3) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 6)))) = Some (Vint32 x4) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 7)))) = Some (Vint32 x5) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 8)))) = Some (Vint32 x6) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 9)))) = Some (Vint32 x7) ->
                 vl = (Vint32 x1 ::Vint32 x2 ::Vint32 x3 ::Vint32 x4 ::Vint32 x5 ::Vint32 x6 ::Vint32 x7 :: nil) ->
                 x' = set_mpax_struct x (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) vl ->
                 store Tint32 M (ses_mpax_block,((Int.unsigned v2)*8)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

| csl_xmc_getXMPAXL_step:
                 forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2: expr)
                        (p:progunit) v1 v2 G E M M1 M2 M3 M4 M5 M6 M7
                        M1' M2' M3' M4' M5' M6' M7' mx M'
                        mx1 mx2 mx3 mx4 mx5 mx6 mx1' mx2' mx3' mx4' mx5' mx6'
                         lst b x y z0 z1 z2 z3 z4 z5 z6,
                  C =((curs (sprim (scsl_xmc_getXMPAXL e1 e2))), (kenil, ks)) ->
                  m = (G,E,M) ->
                  evaltype e1 m = Some Tint32 ->
                  evaltype e2 m = Some (Tptr XMC_XMPAXL) ->
                  evalval e1 m = Some (Vint32 v1) ->
                  evalval e2 m = Some (Vptr v2) ->
                  Vint32 v1 <> Vundef ->
                  Vptr v2 <> Vundef ->
                  v2 = (b,y) -> 
                  load Tint32 M (xmpax_block,((Int.unsigned v1)*8)%Z) = Some (Vint32 x) ->
                  mapstoval (b, ((Int.unsigned y) + 0)%Z) Tint32 true (Vint32 z0) M1 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 4)))) Tint8 true (Vint32 z1) M2 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 5)))) Tint8 true (Vint32 z2) M3 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 6)))) Tint8 true (Vint32 z3) M4 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 7)))) Tint8 true (Vint32 z4) M5 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 8)))) Tint8 true (Vint32 z5) M6 ->
                  mapstoval (b, (Int.unsigned (Int.add y (Int.repr 9)))) Tint8 true (Vint32 z6) M7 ->
                  join M2 M1 mx1 /\ join M3 mx1 mx2 /\ join M4 mx2 mx3 /\ join M5 mx3 mx4 /\
                  join M6 mx4 mx5 /\ join M7 mx5 mx6 /\ join mx6 mx M ->
                  store Tint32 M1 (b,((Int.unsigned y) + 0)%Z) (Vint32 (get_mpax x xmc_raddr)) = Some M1' ->
                  store Tint8 M2 (b,(Int.unsigned (Int.add y (Int.repr 4)))) (Vint32 (get_mpax x xmc_sr)) = Some M2' ->
                  store Tint8 M3 (b,(Int.unsigned (Int.add y (Int.repr 5)))) (Vint32 (get_mpax x xmc_sw)) = Some M3' ->
                  store Tint8 M4 (b,(Int.unsigned (Int.add y (Int.repr 6)))) (Vint32 (get_mpax x xmc_sx)) = Some M4' ->
                  store Tint8 M5 (b,(Int.unsigned (Int.add y (Int.repr 7)))) (Vint32 (get_mpax x xmc_ur)) = Some M5' ->
                  store Tint8 M6 (b,(Int.unsigned (Int.add y (Int.repr 8)))) (Vint32 (get_mpax x xmc_uw)) = Some M6' ->
                  store Tint8 M7 (b,(Int.unsigned (Int.add y (Int.repr 9)))) (Vint32 (get_mpax x xmc_ux)) = Some M7' ->
                  join M2' M1' mx1' /\ join M3' mx1' mx2' /\ join M4' mx2' mx3' /\ join M5' mx3' mx4' /\
                  join M6' mx4' mx5' /\ join M7' mx5' mx6' /\ join mx6' mx M' ->
                  m' = (G,E,M') ->
                  loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_xmc_setXMPAXL_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2: expr)
                                                           (p:progunit) v1 v2 G E M M1 lst b x x' x1 x2 x3 x4 x5 x6 x7 y vl,
                 C =((curs (sprim (scsl_xmc_setXMPAXL e1 e2))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some (Tptr XMC_XMPAXL) ->
                 evalval e1 m = Some (Vint32 v1) ->
                 evalval e2 m = Some (Vptr v2) ->
                 Vint32 v1 <> Vundef ->
                 Vptr v2 <> Vundef ->
                 load Tint32 M (xmpax_block,((Int.unsigned v1)*8)%Z) = Some (Vint32 x) ->
                 v2 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 5)))) = Some (Vint32 x3) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 6)))) = Some (Vint32 x4) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 7)))) = Some (Vint32 x5) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 8)))) = Some (Vint32 x6) ->
                  load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 9)))) = Some (Vint32 x7) ->
                 vl = (Vint32 x1 ::Vint32 x2 ::Vint32 x3 ::Vint32 x4 ::Vint32 x5 ::Vint32 x6 ::Vint32 x7 :: nil) ->
                 x' = set_mpax_struct x (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) vl ->
                 store Tint32 M (xmpax_block,((Int.unsigned v1)*8)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_msmc_setSMSMPAXH_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                                                           (p:progunit) v1 v2 v3 G E M M1 lst b x x' x1 x2 y vl,
                 C =((curs (sprim (scsl_msmc_setSMSMPAXH e1 e2 e3))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some Tint32 ->
                 evaltype e3 m = Some (Tptr MSMC_SMSMPAXH) ->
                 evalval e1 m = Some v1 ->
                 evalval e2 m = Some (Vint32 v2) ->
                 evalval e3 m = Some (Vptr v3) ->
                 v1 <> Vundef ->
                 Vint32 v2 <> Vundef ->
                 Vptr v3 <> Vundef ->
                 load Tint32 M (sms_mpax_block,((Int.unsigned v2)*8 + 4)%Z) = Some (Vint32 x) ->
                 v3 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                 vl = (Vint32 x1 ::Vint32 x2  :: nil) ->
                 x' = set_mpax_struct x (smsh_baddr :: smsh_segsize :: nil) vl ->
                 store Tint32 M (sms_mpax_block,((Int.unsigned v2)*8 + 4)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_msmc_setSESMPAXH_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2 e3: expr)
                                                           (p:progunit) v1 v2 v3 G E M M1 lst b x x' x1 x2 y vl,
                 C =((curs (sprim (scsl_msmc_setSESMPAXH e1 e2 e3))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some Tint32 ->
                 evaltype e3 m = Some (Tptr MSMC_SESMPAXH) ->
                 evalval e1 m = Some v1 ->
                 evalval e2 m = Some (Vint32 v2) ->
                 evalval e3 m = Some (Vptr v3) ->
                 v1 <> Vundef ->
                 Vint32 v2 <> Vundef ->
                 Vptr v3 <> Vundef ->
                 load Tint32 M (ses_mpax_block,((Int.unsigned v2)*8 + 4)%Z) = Some (Vint32 x) ->
                 v3 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                 vl = (Vint32 x1 ::Vint32 x2  :: nil) ->
                 x' = set_mpax_struct x (sesh_baddr :: sesh_segsize :: nil) vl ->
                 store Tint32 M (ses_mpax_block,((Int.unsigned v2)*8 + 4)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_xmc_setXMPAXH_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)(e1 e2: expr)
                                                           (p:progunit) v1 v2 G E M M1 lst b x x' x1 x2 y vl,
                 C =((curs (sprim (scsl_xmc_setXMPAXH e1 e2))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 evaltype e1 m = Some Tint32 ->
                 evaltype e2 m = Some (Tptr XMC_XMPAXH) ->
                 evalval e1 m = Some (Vint32 v1) ->
                 evalval e2 m = Some (Vptr v2) ->
                 Vint32 v1 <> Vundef ->
                 Vptr v2 <> Vundef ->
                 load Tint32 M (xmpax_block,((Int.unsigned v1)*8 + 4)%Z) = Some (Vint32 x) ->
                 v2 = (b,y) ->
                 load Tint32 M (b,((Int.unsigned y) + 0)%Z) = Some (Vint32 x1) ->
                 load Tint8 M (b,(Int.unsigned (Int.add y (Int.repr 4)))) = Some (Vint32 x2) ->
                 vl = (Vint32 x1 ::Vint32 x2  :: nil) ->
                 x' = set_mpax_struct x (xmc_baddr :: xmc_segsize :: nil) vl ->
                 store Tint32 M (xmpax_block,((Int.unsigned v1)*8 + 4)%Z) (Vint32 x') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_xmc_clearFault_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)
                                                           (p:progunit) vfar vfsr vfsr' G E M M1 M2 lst,
                 C =((curs (sprim (scsl_xmc_clearFault))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 load Tint32 M (xmpfar_block,0%Z) = Some (Vint32 vfar) ->
                 load Tint32 M (xmpfsr_block,0%Z) = Some (Vint32 vfsr) ->
                 vfsr' = set_part (set_part vfsr 26%nat 0%nat Int.zero) 23%nat 8%nat Int.zero ->
                 store Tint32 M (xmpfar_block,0%Z) (Vint32 Int.zero) = Some M1 ->
                 store Tint32 M1 (xmpfsr_block,0%Z) (Vint32 vfsr') = Some M2 ->
                 m' = (G,E,M2) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)

 | csl_cgem_clearMDMAError_step: forall (C:code) (ks:stmtcont) (m m': smem) (ir:isr)(er:ier)
                                                           (p:progunit) verr verr' G E M M1 lst,
                 C =((curs (sprim (scsl_cgem_clearMDMAError))), (kenil, ks)) ->
                 m = (G,E,M) ->
                 load Tint32 M (mdmaerr_block,0%Z) = Some (Vint32 verr) ->
                 verr' = set_part (set_part (set_part verr 29%nat 0%nat Int.zero) 20%nat 8%nat Int.zero) 0%nat 29%nat Int.zero ->
                 store Tint32 M (mdmaerr_block,0%Z) (Vint32 verr') = Some M1 ->
                 m' = (G,E,M1) ->
                 loststep p C (m, ir, er, lst)  (SKIP, (kenil, ks)) (m', ir, er, lst)
.

Open Scope nat_scope.

Definition INTNUM_MIN := 4%nat.

Inductive lintstep : intunit -> code -> taskst -> code -> taskst ->Prop:=
| li_step : forall (C:code) (c:cureval) (ke:exprcont) (ks:stmtcont) (ir:isr) (er:ier) (si:is) (i i':hid) (s:stmts)
                   (theta:intunit) ge le m,
              C=(c, (ke, ks)) -> 
              i<INUM -> theta i = Some s ->
              i >= INTNUM_MIN -> er i = true -> 
              lintstep theta C ((ge,le,m) , ir, er, (true, si, nil)) 
                       ((curs s), (kenil, (kint c ke le ks))) 
                       ((ge,emp,m), (isrupd ir i true) , er, (false, (cons i si), nil))
| lnmi_step : forall (C:code) (c:cureval) (ke:exprcont) (ks:stmtcont) (ir:isr) (er:ier) (si:is) (i i':hid) (s:stmts)
                     (theta:intunit) ge le m ie,
              C=(c, (ke, ks)) -> 
              theta i = Some s ->
              i=1->
              (*i < INTNUM_MIN ->*) er i = true -> 
              lintstep theta C ((ge,le,m) , ir, er, (ie, si, nil)) 
                  ((curs s), (kenil, (kint c ke le ks))) 
                  ((ge,emp,m), (isrupd ir i true) , (ierupd er i false), (false, (cons i si), nil)).


Definition InOS (C:code) (p:progunit) : Prop :=
  exists (c:cureval) (ke:exprcont) (ks:stmtcont), 
    C= (c, (ke, ks)) /\ (
      (exists (f:fid) (vl:vallist) (fc:function) tl,  
         c = curs (sfexec f vl tl) /\ p f =Some fc) \/
      (exists (f:fid) (le:env) (ks':stmtcont) (t:type) (d1 d2:decllist) (s:stmts) s',
         callcont ks = Some (kcall f s le ks')/\ p f = Some (t,d1,d2,s') )\/
      ~(intcont ks = None)
    ).

Parameter pdata: var.

Inductive ltstep: lprog -> tid -> code -> clientst -> taskst -> code -> 
                  clientst -> taskst -> Prop :=
| clt_step: forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) 
                   (m m':smem)(cenvs:cltenvs) 
                   (ge le le':env) (M M':mem) (t:tid) (cst cst':clientst) (tst:taskst),
              p= (pc, (po, pi, ip)) -> 
              cstep (pumerge pc po) C m C' m' ->
              ~ (InOS C (pumerge po pi)) -> 
              m = (ge, le, M) -> m' = (ge, le', M') ->
              get cenvs t = Some le ->
              cst = (ge,cenvs, M) -> cst'= (ge, ( set cenvs t le'), M') -> 
              ltstep p t C cst tst C' cst' tst

| inapi_step : forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) 
                      (cst:clientst) (tst tst':taskst) (t:tid),
                 p= (pc, (po, pi, ip)) -> 
                 loststep (pumerge po pi) C tst C' tst' -> 
                 InOS C (pumerge po pi) ->
                 ltstep p t C cst tst C' cst tst'.      

Inductive ltstepev: lprog -> tid -> code -> clientst -> taskst -> code -> 
                    clientst -> taskst -> val -> Prop :=
| clt_stepev: forall (p:lprog)(pc po pi:progunit) (ip:intunit) (C C':code) (v:val)
                     (m :smem)  (cenvs:cltenvs) 
                     (ge le:env) (M :mem) (t:tid) (cst :clientst) (tst:taskst),
                p=(pc, (po, pi, ip)) -> 
                cstepev (pumerge pc po) C m C' m v ->
                ~ (InOS C (pumerge po pi)) -> 
                m = (ge, le, M) -> 
                cst = (ge, cenvs, M ) -> 
                get cenvs t = Some le ->
                ltstepev p t C cst tst C' cst tst v.  

Definition loststepabt (p:progunit) (C:code) (tst: taskst) : Prop := 
  ~(exists C' tst', loststep p C tst C' tst').



Inductive ltstepabt: lprog -> tid -> code -> clientst -> taskst -> Prop :=
| taskabort: forall  (p:lprog) (t:tid) (pc po pi:progunit)(cst:clientst) (ip:intunit) (C:code)
                     (tst:taskst),
               p=(pc, (po, pi, ip)) ->  
               ~((exists (C':code) (tst':taskst) (cst':clientst), ltstep p t C cst tst C' cst' tst')
                 \/(exists (C':code) (tst':taskst) (cst':clientst) ev, ltstepev p t C cst tst C' cst' tst' ev)
                )-> ltstepabt p t C cst tst.

Definition ZofINTNUM := 16%Z. 

Inductive lpstep: lprog -> tasks -> clientst -> osstate -> tid -> 
                  tasks -> clientst -> osstate ->tid -> Prop :=
| pint_step : forall (pc pi po:progunit) (ip:intunit) (p:lprog) (T T':tasks) (cst:clientst)
                     (S S':osstate) (t:tid) (tst tst':taskst) (C C':code),
                p=(pc, (po, pi, ip)) ->
                get T t = Some C ->  set T t C'= T'->
                projS S t = Some tst -> projS S' t = Some tst'-> Steq S S' t->
                lintstep ip C tst C' tst' ->
                lpstep p T cst S t T' cst S' t

| pt_step : forall (p:lprog) (T T':tasks) (S S':osstate) (t:tid) 
                   (tst tst':taskst)(C C':code) 
                   (cst cst':clientst)  ,
              get T t = Some C ->  set T t C'= T'->
              projS S t =Some tst -> projS S' t =Some tst' ->
              Steq S S' t ->
              ltstep p t C cst tst C' cst' tst' ->
              lpstep p T cst S t T' cst' S' t
| pswitch_step: forall (p:lprog) pc po pi ip (T T':tasks) (x:var)  (S S':osstate) (cst:clientst) (t t':tid) (ks:stmtcont) (tst:taskst) l tp b ge les m m' ir er au,
                  p =(pc,(po,pi,ip)) ->
                  (*InOS ((curs (sprim (switch x))), (kenil, ks))  (pumerge po pi) ->*)
                  projS S t = Some tst ->
                  get (get_genv (get_smem tst)) x = Some (l,(Tptr tp)) ->
                  load (Tptr tp) (get_mem (get_smem tst)) (l,0%Z) = Some (Vptr t')-> 
                  get T t = Some ((curs (sprim (switch x))), (kenil, ks)) ->
                  set T t (SKIP, (kenil, ks))= T'->
                  S = (ge,les,m,ir,er,au) ->
                  S' = (ge,les,m',ir,er,au)->
                  get ge OSTCBCur = Some (b,(Tptr tp)) ->
                  store (Tptr tp) m (b,0%Z) (Vptr t') = Some m'-> 
                  lpstep p T cst S t T' cst S' t'
| pstkinit_step: forall (p:lprog) (T T':tasks) (S:osstate) (t t':tid) (tst:taskst)(C C':code) 
                        (cst cst':clientst)  (ks:stmtcont) (e1 e2 e3:expr)
                        (tau:type) (d1 d2:decllist) (s:stmts) (pc pi po:progunit) (ip:intunit) (f:fid) v1 v m_os ir er au cenvs M M' ge le,
                   p=(pc, (po, pi, ip)) ->
                   get T t = Some C ->
                   C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
                   C'= (SKIP, (kenil, ks))->
                   set T t C'= T'->
                   evalval e1 m_os = Some v1 ->
                   evalval e2 m_os = Some v -> 
                   evalval e3 m_os = Some (Vptr t')->
                   vtoZ v1 =Some f ->
                   pc f = Some (tau, d1, d2, s) ->
                   cstepstar pc ((curs (sfexec f (cons v nil) ((Tptr Tvoid)::nil))), (kenil, kstop))
                             (ge,emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M') ->
                   evaltype e2 m_os = Some (Tptr Tvoid) ->
                   tst =(m_os, ir, er, au) ->
                   projS S t =Some tst ->
                   cst = (ge, cenvs, M) ->
                   cst'=(ge, ( set cenvs t' le), M') ->
                   lpstep p T cst S t ( set T' t' (nilcont s)) cst' (Snewt S t') t
| pstkinitskip_step: forall (p:lprog) (T T':tasks) (S :osstate) (t t':tid) (tst:taskst)(C C':code) 
                            (cst:clientst)  (ks:stmtcont) (e1 e2 e3:expr)
                            (pc pi po:progunit) (ip:intunit) (f:fid) v1 v m_os ir er au cenvs M ge,
                       p=(pc, (po, pi, ip)) ->
                       get T t = Some C ->
                       C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
                       C'= (SKIP, (kenil, ks))->
                       set T t C'= T'->
                       evalval e1 m_os = Some v1 ->
                       evalval e2 m_os = Some v -> 
                       evalval e3 m_os = Some (Vptr t')->
                       vtoZ v1 =Some f ->
                       (pc f = None \/ 
                        (exists t d1 d2 s,
                           pc f = Some (t ,d1,d2,s) /\
                           ~(exists le M', cstepstar pc ((curs (sfexec f (cons v nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) (ge, emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M')))) ->
                       evaltype e2 m_os = Some (Tptr Tvoid) ->
                       tst =(m_os, ir, er, au) ->
                       projS S t =Some tst ->
                       cst = (ge, cenvs, M) ->
                       lpstep p T cst S t ( set T' t' (nilcont (sskip None))) cst (Snewt S t') t

| pstkfree_step: forall T T' C C' (ks:stmtcont) (m:smem) (e:expr) (t':tid) (pc po pi:progunit) (ip:intunit)
                        (ir:isr) (er:ier) (au:localst) (p:lprog) D ge cenvs M D' t S,
                   p= (pc, (po, pi, ip)) ->
                   get T t = Some C ->
                   C =(curs (sprim (stkfree e)), (kenil, ks)) ->
                   C'= (SKIP, (kenil, ks))->
                   set T t C'= T'->
                   D = (ge,cenvs,M) ->
                   D' = (ge, (del cenvs t'), M)->
                   evalval e m = Some (Vptr t') ->
                   projS S t = Some (m,ir,er,au) ->
                   lpstep p T D S t T' D' S t.


Inductive lpstepev: lprog -> tasks -> clientst -> osstate -> tid -> 
                    tasks -> clientst -> osstate ->tid -> val -> Prop :=
| pt_stepev :  forall (p:lprog) (T T':tasks) (S :osstate) (t :tid)
                      (tst:taskst)
                      (cst:clientst) (c:cureval) (C C':code) 
                      (ev:val), 
                 get T t = Some C ->  set T t C'= T'->
                 projS S t =Some tst ->
                 ltstepev p t C cst tst C' cst tst ev ->
                 lpstepev p T cst S t T' cst S t ev.

Definition IsEnd (C : code) : Prop := exists v, C = (curs (sskip v), (kenil, kstop)).

Definition IsSwitch (C : code) : Prop := exists x ks,
                                           C = (curs (sprim (switch x)),(kenil, ks)).

Definition IsFcall (C:code) : Prop := exists f vl tl ks,
                                        C = (curs (sfexec f vl tl), (kenil,ks)).

Definition IsRet (C : code) : Prop := (exists ks, C = (curs sret, (kenil, ks))
                                                  /\ callcont ks = None/\intcont ks =None).

Definition IsRetE (C : code) : Prop := (exists v ks, C = ([v], (kenil , 
                                                                (kret ks)))/\
                                                     callcont ks = None/\intcont ks =None).

Definition IsIRet (C : code) : Prop := (exists ks, C = (curs (sprim exint), (kenil, ks)) /\ intcont ks = None/\callcont ks =None).


Definition IsStkInit (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))).

Definition IsStkFree (C:code):= (exists e ks, C = (curs (sprim (stkfree e)),(kenil,ks))).

Definition IsDint (C:code):= (exists level ks, C = (curs (sprim (dint level)),(kenil,ks))).

Definition IsRint (C:code):= (exists level ks, C = (curs (sprim (rint level)),(kenil,ks))).

Definition IsDintp (C:code) : Prop := (exists irqLine ks, C = (curs (sprim (dintp irqLine)),(kenil,ks))).

Definition IsRintp (C:code):= (exists irqLine ks, C = (curs (sprim (rintp irqLine)),(kenil,ks))).

Definition IsSgenerateipc (C:code):= (exists e1 e2 ks, C = (curs (sprim (sgenerateipc e1 e2)),(kenil,ks))).

Definition IsSclearipc (C:code):= (exists e1 e2 ks, C = (curs (sprim (sclearipc e1 e2)),(kenil,ks))).

Definition IsSgetsem (C:code):= (exists e ks, C = (curs (sprim (sgetsem e)),(kenil,ks))).

Definition IsSpostsem (C:code):= (exists e ks, C = (curs (sprim (spostsem e)),(kenil,ks))).

Definition IsScslsemacc (C:code):= (exists e1 e2 ks, C = (curs (sprim (scsl_semaccdir e1 e2)),(kenil,ks))).

Definition IsScslsemrel (C:code):= (exists e ks, C = (curs (sprim (scsl_semrel e)),(kenil,ks))).

Definition IsScsl_msmc_getSMSMPAXL (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_getSMSMPAXL e1 e2 e3)),(kenil,ks))).

Definition IsScsl_msmc_setSMSMPAXL (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_setSMSMPAXL e1 e2 e3)),(kenil,ks))).

Definition IsScsl_msmc_getSESMPAXL (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_getSESMPAXL e1 e2 e3)),(kenil,ks))).

Definition IsScsl_msmc_setSESMPAXL (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_setSESMPAXL e1 e2 e3)),(kenil,ks))).

Definition IsScsl_xmc_getXMPAXL (C:code):= (exists e1 e2 ks, C = (curs (sprim (scsl_xmc_getXMPAXL e1 e2)),(kenil,ks))).

Definition IsScsl_xmc_setXMPAXL (C:code):= (exists e1 e2 ks, C = (curs (sprim (scsl_xmc_setXMPAXL e1 e2)),(kenil,ks))).

Definition IsScsl_msmc_setSMSMPAXH (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_setSMSMPAXH e1 e2 e3)),(kenil,ks))).

Definition IsScsl_msmc_setSESMPAXH (C:code):= (exists e1 e2 e3 ks, C = (curs (sprim (scsl_msmc_setSESMPAXH e1 e2 e3)),(kenil,ks))).

Definition IsScsl_xmc_setXMPAXH (C:code):= (exists e1 e2 ks, C = (curs (sprim (scsl_xmc_setXMPAXH e1 e2)),(kenil,ks))).

Definition IsScsl_xmc_clearFault (C:code):= (exists ks, C = (curs (sprim (scsl_xmc_clearFault)),(kenil,ks))).

Definition IsScsl_cgem_clearMDMAError (C:code):= (exists ks, C = (curs (sprim (scsl_cgem_clearMDMAError)),(kenil,ks))).

Inductive lpstepabt: lprog ->  tasks -> clientst -> osstate -> tid -> Prop:=
| progabort: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                    (cst:clientst)(C:code) (v : option val) ,
               get T t = Some C -> 
               projS S t =Some tst ->
               ~ IsSwitch C ->
               ~ IsStkInit C ->
               ~ IsStkFree C ->
               ~ IsEnd C ->
               ltstepabt p t C cst tst ->
               lpstepabt p T cst S t
| crt_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                  (cst:clientst)(C:code) e1 e2 e3 ks ,
               get T t = Some C -> 
               projS S t =Some tst ->
               C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks)) ->
               (~ exists v1 v t',
                    evalval e1 (get_smem tst) = Some v1 /\
                    evalval e2 (get_smem tst) = Some v /\
                    evalval e3 (get_smem tst) = Some (Vptr t')
               ) ->
               lpstepabt p T cst S t
| del_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                  (cst:clientst)(C:code) e ks,
               get T t = Some C -> 
               projS S t =Some tst ->
               C = (curs (sprim (stkfree e)),(kenil,ks)) ->
               (~ exists t',
                    evalval e (get_smem tst) = Some (Vptr t')
               )  ->
               lpstepabt p T cst S t
| switch_abt: forall (p:lprog) (T :tasks) (S :osstate) (t:tid) (tst :taskst) 
                     (cst:clientst)(C:code) x ks,
                get T t = Some C -> 
                projS S t =Some tst ->
                C = (curs (sprim (switch x)),(kenil,ks)) ->
                (~ exists l tp t',
                     get (get_genv (get_smem tst)) x = Some (l,(Tptr tp)) /\
                     load (Tptr tp) (get_mem (get_smem tst)) (l,0%Z) = Some (Vptr t') 
                )  ->
                lpstepabt p T cst S t.

(****)
Definition eqdomtls (tls tls':TcbMod.map):=
  forall tid, indom tls tid <-> indom tls' tid.


Definition eqdomO (O O':osabst):= (forall (x:absdataid), indom O x <-> indom O' x) /\
                                  ( forall tls,  get O abstcblsid = Some (abstcblist tls) ->
                                                 exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls' ).
(*
Definition eqdomO (O O':osabst):= (forall x,  indom O x <->  indom O' x) /\
                                  ( (~ exists tls,  get O abstcblsid = Some (abstcblist tls)) \/
                                    exists tls tls',  get O abstcblsid = Some (abstcblist tls) /\
                                                      get O' abstcblsid = Some (abstcblist tls') /\
                                                     eqdomtls tls tls' ).
 *)
Definition tidsame (O O':osabst):=  get O curtid =  get O' curtid.

Inductive spec_step: ossched -> spec_code -> osabst -> spec_code -> osabst -> Prop :=
| spec_prim_step:
    forall sc O O' (step:osabstep) v Of vl OO OO',
      step vl O (v, Some O') ->
      eqdomO O O' ->
      tidsame O O' ->
      join O Of OO ->
      join O' Of OO' ->
      spec_step sc (spec_prim vl step) OO (spec_done v) OO'

| spec_prim_step_abt:
    forall sc O (step: osabstep) v Of vl OO,
      step vl O (v, None) ->
      join O Of OO ->
      spec_step sc (spec_prim vl step) OO spec_abort OO 
                
| spec_seq_step1:
    forall v cd O sc,
      spec_step sc (spec_seq (spec_done v) cd) O cd O 

| spec_seq_step1':
  forall cd O sc,
    spec_step sc (spec_seq spec_abort cd) O spec_abort O 

| spec_seq_step2:
    forall O O' s1 s2 s1' sc,
      spec_step sc s1 O s1' O' ->
      spec_step sc (spec_seq s1 s2) O (spec_seq s1' s2) O'

| spec_choice_step1:
    forall O s1 s2 sc,
      spec_step sc (spec_choice s1 s2) O s1 O

| spec_choice_step2:
    forall O s1 s2 sc,
      spec_step sc (spec_choice s1 s2) O s2 O

| spec_assume_step:
    forall O Of (b:absexpr) OO sc ,
      b O ->
      join O Of OO ->
      spec_step sc (spec_assume b)  OO  (spec_done None) OO
                
| spec_assert_step_cont:
  forall O Of (b:absexpr) OO sc,
    b O ->
    join O Of OO ->
    spec_step sc (spec_assert b) OO (spec_done None) OO

| spec_assert_step_abt:
    forall O Of (b:absexpr) OO sc ,
      ~(b O) ->
      join O Of OO -> 
      spec_step sc (spec_assert b) OO spec_abort OO  

| spec_sched_step:
    forall t O Of OO (sc:ossched),
      get O curtid = Some (oscurt t) ->
      sc O t -> 
      join O Of OO ->
      spec_step sc sched OO (spec_done None) OO
      
| spec_coreint_step:
    forall sc O Of OO n m,
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
      spec_step sc (coreint n m) OO (spec_done None) OO 
      
| spec_getsem_step:
    forall sc O Of OO i,
    (Z.of_nat i <= Int.max_unsigned)%Z ->
    join O Of OO ->
      spec_step sc (getsem i) OO (spec_done None) OO
      
| spec_postsem_step:
    forall sc O Of OO i,
    (Z.of_nat i <= Int.max_unsigned)%Z ->
    join O Of OO ->
      spec_step sc (postsem i) OO (spec_done None) OO  
      
| spec_clearipc_step:
    forall sc O Of OO O' OO' n m,
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    join O Of OO ->
    get O ipcgrid = Some (osipcgr m) ->
    O' = set O ipcgrid (osipcgr (Vint32 Int.zero)) ->
    join O' Of OO' ->
    spec_step sc (clearipc n  m) OO (spec_done None) OO'    

| spec_cslsemacc_step:
    forall sc O Of OO n m,
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    (m = Vint32 Int.zero \/ m = Vint32 Int.one) ->
    join O Of OO ->
      spec_step sc (cslsemacc n m) OO (spec_done None) OO      

| spec_cslsemrel_step:
    forall sc O Of OO n,
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    join O Of OO ->
      spec_step sc (cslsemrel n) OO (spec_done None) OO     

| spec_csl_msmc_getSMSMPAXL_step:
    forall sc O Of OO n m q index
    sms mpaxl mpaxh strheap vl vl' strheap0 O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    get O sms_mpaxid = Some (ossms_mpax sms) ->
    SmsMod.get sms index = Some (mpaxl,mpaxh) ->
    vl' = get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) ->
    strheap0 = Set_struct strheap q MSMC_SMSMPAXL vl' ->
    O' = set O evstructheapid (evstructheap strheap0) ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_getSMSMPAXL n m q) OO (spec_done None) OO'

| spec_csl_msmc_setSMSMPAXL_step:
    forall sc O Of OO n m q index sms sms' mpaxl mpaxl' mpaxh
    raddr sr sw sx ur uw ux strheap vl O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    vl = (Vint32 raddr :: Vint32 sr :: Vint32 sw :: Vint32 sx :: Vint32 ur :: Vint32 uw ::Vint32 ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) ->
    get O sms_mpaxid = Some (ossms_mpax sms) ->
    SmsMod.get sms index = Some (mpaxl, mpaxh) ->
    mpaxl' = set_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) vl ->
    sms' = SmsMod.set sms index (mpaxl', mpaxh) ->
    O' = set O sms_mpaxid (ossms_mpax sms') ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_setSMSMPAXL n m q) OO (spec_done None) OO'

| spec_csl_msmc_getSESMPAXL_step:
    forall sc O Of OO n m q index
    ses mpaxl mpaxh strheap vl vl' strheap0 O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    get O ses_mpaxid = Some (osses_mpax ses) ->
    SesMod.get ses index = Some (mpaxl,mpaxh) ->
    vl' = get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) ->
    strheap0 = Set_struct strheap q MSMC_SESMPAXL vl' ->
    O' = set O evstructheapid (evstructheap strheap0) ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_getSESMPAXL n m q) OO (spec_done None) OO'

| spec_csl_msmc_setSESMPAXL_step:
    forall sc O Of OO n m q index ses ses' mpaxl mpaxl' mpaxh
    raddr sr sw sx ur uw ux strheap vl O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    vl = (Vint32 raddr :: Vint32 sr :: Vint32 sw :: Vint32 sx :: Vint32 ur :: Vint32 uw ::Vint32 ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) ->
    get O ses_mpaxid = Some (osses_mpax ses) ->
    SesMod.get ses index = Some (mpaxl, mpaxh) ->
    mpaxl' = set_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) vl ->
    ses' = SesMod.set ses index (mpaxl', mpaxh) ->
    O' = set O ses_mpaxid (osses_mpax ses') ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_setSESMPAXL n m q) OO (spec_done None) OO' 

| spec_csl_xmc_getXMPAXL_step:
    forall sc O Of OO n q index
    xmc mpaxl mpaxh strheap vl vl' strheap0 O' OO',
    join O Of OO ->
    n = Vint32 index ->
    get O xmpaxid = Some (osxmpax xmc) ->
    XmcMod.get xmc index = Some (mpaxl,mpaxh) ->
    vl' = get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, XMC_XMPAXL, vl) ->
    strheap0 = Set_struct strheap q XMC_XMPAXL vl' ->
    O' = set O evstructheapid (evstructheap strheap0) ->
    join O' Of OO' ->
    spec_step sc (csl_xmc_getXMPAXL n q) OO (spec_done None) OO'
    
| spec_csl_xmc_setXMPAXL_step:
    forall sc O Of OO n q index xmc xmc' mpaxl mpaxl' mpaxh
    raddr sr sw sx ur uw ux strheap vl O' OO',
    join O Of OO ->
    n = Vint32 index ->
    vl = (Vint32 raddr :: Vint32 sr :: Vint32 sw :: Vint32 sx :: Vint32 ur :: Vint32 uw ::Vint32 ux :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, XMC_XMPAXL, vl) ->
    get O xmpaxid = Some (osxmpax xmc) ->
    XmcMod.get xmc index = Some (mpaxl, mpaxh) ->
    mpaxl' = set_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) vl ->
    xmc' = XmcMod.set xmc index (mpaxl', mpaxh) ->
    O' = set O xmpaxid (osxmpax xmc') ->
    join O' Of OO' ->
    spec_step sc (csl_xmc_setXMPAXL n q) OO (spec_done None) OO' 

| spec_csl_msmc_setSMSMPAXH_step:
    forall sc O Of OO n m q index sms sms' mpaxl mpaxh mpaxh'
    bAddr segSz strheap vl O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    vl = (Vint32 bAddr :: Vint32 segSz :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SMSMPAXH, vl) ->
    get O sms_mpaxid = Some (ossms_mpax sms) ->
    SmsMod.get sms index = Some (mpaxl, mpaxh) ->
    mpaxh' = set_mpax_struct mpaxh (smsh_baddr :: smsh_segsize :: nil) vl ->
    sms' = SmsMod.set sms index (mpaxl, mpaxh') ->
    O' = set O sms_mpaxid (ossms_mpax sms') ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_setSMSMPAXH n m q) OO (spec_done None) OO'

| spec_csl_msmc_setSESMPAXH_step:
    forall sc O Of OO n m q index ses ses' mpaxl mpaxh mpaxh'
    bAddr segSz strheap vl O' OO',
    join O Of OO ->
    (Z.of_nat n <= Int.max_unsigned)%Z ->
    m = Vint32 index ->
    vl = (Vint32 bAddr :: Vint32 segSz :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, MSMC_SESMPAXH, vl) ->
    get O ses_mpaxid = Some (osses_mpax ses) ->
    SesMod.get ses index = Some (mpaxl, mpaxh) ->
    mpaxh' = set_mpax_struct mpaxh (sesh_baddr :: sesh_segsize :: nil) vl ->
    ses' = SesMod.set ses index (mpaxl, mpaxh') ->
    O' = set O ses_mpaxid (osses_mpax ses') ->
    join O' Of OO' ->
    spec_step sc (csl_msmc_setSESMPAXH n m q) OO (spec_done None) OO'

| spec_csl_xmc_setXMPAXH_step:
    forall sc O Of OO n q index xmc xmc' mpaxl mpaxh mpaxh'
    bAddr segSz strheap vl O' OO',
    join O Of OO ->
    n = Vint32 index ->
    vl = (Vint32 bAddr :: Vint32 segSz :: nil) ->
    get O evstructheapid = Some (evstructheap strheap) ->
    Get_struct strheap q = Some (q, XMC_XMPAXH, vl) ->
    get O xmpaxid = Some (osxmpax xmc) ->
    XmcMod.get xmc index = Some (mpaxl, mpaxh) ->
    mpaxh' = set_mpax_struct mpaxh (xmc_baddr :: xmc_segsize :: nil) vl ->
    xmc' = XmcMod.set xmc index (mpaxl, mpaxh') ->
    O' = set O xmpaxid (osxmpax xmc') ->
    join O' Of OO' ->
    spec_step sc (csl_xmc_setXMPAXH n q) OO (spec_done None) OO'

| spec_csl_xmc_clearFault_step:
    forall sc O Of OO vfar  vfsr vfsr' O' O'' OO',
    join O Of OO ->
    get O xmpfarid = Some (xmpfar vfar) ->
    get O xmpfsrid = Some (xmpfsr vfsr) ->
    vfsr' = set_part (set_part vfsr 26%nat 0%nat Int.zero) 23%nat 8%nat Int.zero ->
    O' = set O xmpfarid (xmpfar Int.zero) ->
    O'' = set O' xmpfsrid (xmpfsr vfsr') ->
    join O'' Of OO' ->
    spec_step sc (csl_xmc_clearFault) OO (spec_done None) OO'

| spec_csl_cgem_clearMDMAError_step:
    forall sc O Of OO verr verr' O' OO',
    join O Of OO ->
    get O mdmaerrid = Some (mdmaerr verr) ->
    verr' = set_part (set_part (set_part verr 29%nat 0%nat Int.zero) 20%nat 8%nat Int.zero) 0%nat 29%nat Int.zero ->
    O' = set O mdmaerrid (mdmaerr verr') ->
    join O' Of OO' ->
    spec_step sc (csl_cgem_clearMDMAError) OO (spec_done None) OO'
.


Inductive spec_stepstar:  ossched -> spec_code -> osabst -> spec_code -> osabst -> Prop :=
| spec_stepO:
    forall c O sc,
      spec_stepstar sc c O c O
| spec_stepS:
    forall c O c' O' c'' O'' sc,
      spec_step sc c O c' O' ->
      spec_stepstar sc c' O' c'' O'' ->
      spec_stepstar sc c O c'' O''.

Inductive hapistep:  osspec -> code -> osabst -> code -> osabst -> Prop:=
| hapienter_step:
    forall (A :osspec) (B:osapispec) (C:osintspec) (D : ossched) (O:osabst) (cd cd':code)
           (ks:stmtcont) (f:fid) (vl:vallist) r tl tp vl',
      A= (B, C, D) ->
      tl_vl_match tl vl = true->
      cd = (curs (sfexec f (List.rev vl) (List.rev tl)), (kenil, ks)) ->
      cd'=  (curs (hapi_code (r (vl ++ vl'))), (kenil, ks))->
      B f = Some (r,(tp,tl)) ->
      hapistep  A cd O cd' O
                
| hidapi_step :
    forall (A :osspec) (O O':osabst)
           ke ks cd cd',
      spec_step (snd A) cd O cd' O' ->
      hapistep A ((curs (hapi_code cd )),(ke, ks)) O ((curs (hapi_code cd')),(ke,ks)) O'

| hapiexit_step :
    forall (A :osspec) (O:osabst)
           ke ks v,
      hapistep A ((curs (hapi_code (spec_done v))),(ke, ks)) O ((curs (sskip v)),(ke,ks)) O
               
| hintex_step: forall  (A :osspec) c ke ks  O,
                 hapistep A  (curs (hapi_code (spec_done None)),(kenil,kevent c ke ks)) O
                          (c,(ke,ks)) O.

Inductive htstep: hprog -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop:=
| htclt_step : forall (p:hprog) (pc:progunit) (A:osspec) (c c':code) (m m':smem)
                      (cenvs:cltenvs)  (ge le le':env) (M M':mem) (t:tid) 
                      (cst cst':clientst) (O:osabst),
                 p= (pc, A) -> 
                 cstep pc c m c' m' -> 
                 m = (ge, le, M) -> m' = (ge, le', M') ->
                 get cenvs t = Some le ->
                 cst = (ge,cenvs, M) ->
                 cst'=  (ge, ( set cenvs t le'), M') ->
                 htstep p t c cst O c' cst' O
| hapi_step : forall (p:hprog)(A: osspec) (pc:progunit) (O O':osabst) (c c':code) (cst:clientst) t,
                p=(pc, A) ->
                hapistep  A c O c' O'->
                htstep p t c cst O c' cst O'.


Inductive htstepev:  hprog  -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> val -> Prop:=
| hclt_stepev : forall (p:hprog) (pc:progunit) (A:osspec) (c c':code) (m :smem)
                       (cenvs:cltenvs)  (ge le:env) (M M':mem) (t:tid) (ev:val)
                       (cst:clientst) (O:osabst),
                  p= (pc, A) -> 
                  cstepev pc c m c' m ev->
                  m = (ge, le, M) ->
                  cst = (ge, cenvs, M) ->
                  get cenvs t = Some le -> 
                  htstepev p t c cst O c' cst O ev.

Definition IsCrt (C:code) := exists v1 v2 v3 scre k, C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), k).
Definition IsDel (C:code) := exists v sdel k, C = (curs (hapi_code (spec_seq (spec_del (Vint32 v)) sdel)), k).
Definition IsSc (C:code) := exists s k, C = (curs (hapi_code (spec_seq sched s)), k).

Inductive htstepabt: hprog -> tid -> code -> clientst -> osabst -> Prop:=
| htstep_abt : forall (p:hprog) (pc:progunit) (A:osspec) (c:code)  (t:tid) 
                      (cst :clientst) (O:osabst),
                 p= (pc, A) ->
                 ~ IsEnd c ->
                 ~ IsCrt c ->
                 ~ IsDel c ->
                 ~ IsSc c ->
                 ~(exists c' cst' O', htstep p t c cst O c' cst' O') ->
                 ~(exists c' cst' O' ev, htstepev p t c cst O c' cst' O' ev) ->
                 htstepabt p t c cst O.

Inductive htstepstar:  hprog  -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop:=
| ht_starO: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t,
              htstepstar p t c cst O c cst O
| ht_starS: forall (p:hprog)  (c c' c'':code) (cst cst' cst'':clientst) (O O' O'':osabst) t,
              htstep p t c cst O c' cst' O' -> htstepstar p t c' cst' O' c'' cst'' O''->
              htstepstar p t c cst O c'' cst'' O''.


Inductive htstepevstar: hprog -> tid -> code -> clientst -> osabst -> 
                        code -> clientst -> osabst -> val -> Prop:=
| htev_stepstar: forall (p:hprog)  (c c' c'' c''':code) 
                        (O O' O'':osabst) (ev:val) cst cst' cst'' t,
                   htstepstar p t c cst O c' cst' O' ->
                   htstepev p t c' cst' O' c'' cst' O' ev ->
                   htstepstar p t c'' cst' O' c''' cst'' O'' ->
                   htstepevstar p t c cst O c''' cst'' O'' ev.

Inductive htstepabtstar: hprog  -> tid ->  code -> clientst -> osabst -> Prop:=
| htabtstar: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t,
               (exists (c':code) (cst':clientst) (O':osabst), 
                  htstepstar p t c cst O c' cst' O' /\
                  htstepabt p t c' cst' O')
               -> htstepabtstar p t c cst O.

Inductive htistep: osintspec -> code  -> osabst -> code  -> osabst -> Prop:=
| hinten_step: forall  (C :osintspec)  (O:osabst) c ke ks (i:hid) l,
                 C i = Some l ->
                 htistep C (c,(ke,ks)) O (curs (hapi_code l),(kenil,kevent c ke ks)) O.


Inductive hpstep: hprog -> tasks -> clientst -> osabst ->  
                  tasks -> clientst -> osabst -> Prop:=
| hp_step: forall (p:hprog) (T T':tasks) (O O':osabst) (cst cst':clientst) 
                  (C C':code) (t:tid),
             get O curtid = Some (oscurt t) ->
             htstep p t C cst O C' cst' O' ->
             get T t = Some C -> T' =  set T t C' ->
             hpstep p T cst O T' cst' O'
                    
| hi_step : forall (p:hprog) pc A  ispec B  (T T':tasks)
                   (O O':osabst) (cst:clientst) 
                   (C C':code) (t:tid),
              p = (pc, (A, ispec, B)) ->
              get O curtid = Some (oscurt t) ->
              get T t = Some C ->
              T' =  set T t C' ->
              htistep ispec C O C' O' ->
              hpstep p T cst O T' cst O'
                     
| hswi_step: forall (p:hprog) pc A B sd (T T':tasks) (cst:clientst) (O:osabst) (t t':tid) C ke ks s,
               p = (pc,(A,B,sd)) ->
               sd O t'->
               get O curtid = Some (oscurt t) ->
               get T t = Some C ->
               C = (curs (hapi_code (spec_seq sched s)), (ke,ks)) ->
               T' =  set T t (curs (hapi_code s),(ke,ks)) ->
               hpstep p T cst O T' cst (set O curtid (oscurt t'))
                      
| hpcrt_step : forall (T:tasks) (O O':osabst) (t t':tid)
                      (s:stmts) (cst cst':clientst)
                      (pc:progunit) (A:osspec) (tau:type) (d1 d2:decllist) 
                      (C C' :code) f tls tls' v1 v2 v3 sus ge le M M' cenvs ke ks scre,
                 get T t = Some C ->
                 C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                 C' = (curs (hapi_code scre), (ke, ks)) ->
                 get O curtid = Some (oscurt t) ->

                 vtoZ v1 =Some f ->
                 
                 pc f = Some (tau, d1, d2, s)->
                 cstepstar pc ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop))
                           (ge,emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M') ->
                 cst = (ge, cenvs, M) ->
                 cst'=(ge, (set cenvs t' le), M') ->
                 
                 get O abstcblsid = Some (abstcblist tls) ->
                 set O abstcblsid (abstcblist tls') = O' ->
                 join tls (sig t' (v3,rdy,Vnull,sus)) tls' ->
                 
                 hpstep (pc, A) T cst O
                        ( set ( set T t C') t' (nilcont s)) 
                        cst' O'
                        
| hpcrtskip_step : forall (T:tasks) (O O':osabst) (t t':tid)
                          (cst:clientst)
                          C C' (pc:progunit) (A:osspec)
                           f tls tls' v1 v2 v3 sus ge M cenvs ke ks scre,
                     get T t = Some C ->
                     C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                     C' = (curs (hapi_code scre), (ke, ks)) ->
                     get O curtid = Some (oscurt t) ->

                     vtoZ v1 =Some f ->
                     
                     (pc f = None \/ 
                      (exists t d1 d2 s,
                         pc f = Some (t ,d1,d2,s) /\
                         ~(exists le M', cstepstar pc ((curs (sfexec f (cons v2 nil) ((Tptr Tvoid)::nil))), (kenil, kstop)) (ge, emp,M) ((curs s), (kenil, (kcall f s emp kstop))) (ge,le,M')))) ->
                     
                    
                     cst = (ge, cenvs, M) ->
                     
                     get O abstcblsid = Some (abstcblist tls) ->
                     set O abstcblsid (abstcblist tls') = O' ->
                     join tls (sig t' (v3,rdy,Vnull,sus)) tls' ->                 
                     hpstep (pc, A) T cst O
                            ( set ( set T t C') t' (nilcont (sskip None))) cst O'
| hpdel_step: forall p T T' t t' C C' sdel ke ks ge cenvs M O O' tls tls' cst cst' prio st msg sus,
                
                   get T t = Some C ->
                   C =(curs (hapi_code (spec_seq (spec_del (Vint32 prio)) sdel)), (ke,ks)) ->
                   C'= (curs (hapi_code sdel), (ke, ks))->
                   set T t C'= T'->
                   cst = (ge,cenvs,M) ->
                   cst' = (ge, (del cenvs t'), M)->
                   get O abstcblsid = Some (abstcblist tls) ->
                   set O abstcblsid (abstcblist tls') = O' ->
                   get tls t' = Some (prio,st,msg,sus) ->
                   join tls' (sig t' (prio,st,msg,sus)) tls->
                   get O curtid = Some (oscurt t) ->
                   hpstep p T cst O T' cst' O'.


Definition abs_crt_step (O : OSAbstMod.map)  O' t t' p:=  
  t <> t' /\
  exists tls tls' sus,
    get O curtid = Some (oscurt t) /\
    get O abstcblsid = Some (abstcblist tls) /\
    joinsig t' (p,rdy,Vnull,sus) tls tls' /\
    O' = set O abstcblsid (abstcblist tls') .

Definition del_task (O : OSAbstMod.map)  O' t p :=
  exists tls tls' st msg sus,
    get O abstcblsid = Some (abstcblist tls) /\
    joinsig  t  (p, st, msg, sus) tls' tls /\ 
    O' = set O abstcblsid (abstcblist tls').

Definition abs_delself_step (O : OSAbstMod.map)  O' t t' p := 
  t = t' /\  get O curtid = Some (oscurt t) /\  del_task O O' t' p.


Definition abs_delother_step (O : OSAbstMod.map)  O' t t' p:=  
  t <>  t' /\  get O curtid = Some (oscurt t) /\  del_task O O' t' p.

Definition abs_dint_step (O : OSAbstMod.map) O' := 
  exists er,
    get O ierid = Some (hier er) /\
    O' = set O ierid (hier (empupd er)).

Definition abs_rint_step (O : OSAbstMod.map) O' level := 
  exists er er',
    get O ierid = Some (hier er) /\
    er' = ierupds_int er level /\
    O' = set O ierid (hier er').

Definition abs_dintp_step (O : OSAbstMod.map) O' id:= 
  exists er er',
    get O ierid = Some (hier er) /\
    er' = ierupd er id false /\
    O' = set O ierid (hier er').
    
Definition abs_rintp_step (O : OSAbstMod.map) O' id:= 
  exists er er',
    get O ierid = Some (hier er) /\
    er' = ierupd er id true /\
    O' = set O ierid (hier er').

Inductive hpstepev: hprog -> tasks -> clientst -> osabst  ->  
                    tasks -> clientst -> osabst -> val -> Prop:=
| hpt_stepev: forall (p:hprog) (T T':tasks) (O:osabst) (cst:clientst) 
                     (C C':code) (t:tid) (ev:val),
                get O curtid = Some (oscurt t) ->
                htstepev p t C cst O C' cst O ev->
                get T t = Some C ->
                T' =  set T t C' ->
                hpstepev p T cst O  T' cst O  ev.

Inductive hpstepabt: hprog -> tasks -> clientst -> osabst -> Prop :=
| hpabt_step : forall (p: hprog) (T :tasks) (cst:clientst) (O:osabst) (t:tid) (C:code),
                 get O curtid = Some (oscurt t) ->
                 get T t = Some C ->
                 htstepabt p t C cst O -> 
                 hpstepabt p T cst O
| hpcreabt_step : forall (T:tasks) (O:osabst) (t:tid)
                         (cst:clientst)
                         p (C :code) v1 v2 v3 ke ks scre,
                    get T t = Some C ->
                    C = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 v3)) scre)), (ke,ks)) ->
                    get O curtid = Some (oscurt t) ->
                    (~ exists O' t', abs_crt_step O O' t t' v3) ->
                    hpstepabt p T cst O
| hpdelabt_step : forall (T:tasks) O t
                         (cst:clientst)
                         p C v ke ks sdel,
                    get T t = Some C ->
                    C = (curs (hapi_code (spec_seq (spec_del (Vint32 v)) sdel)), (ke,ks)) ->
                    get O curtid = Some (oscurt t) ->
                    (~ exists O' t', abs_delself_step O O' t t' v \/ abs_delother_step O O' t t' v) ->
                    hpstepabt p T cst O
| hscabt_step: forall (T:tasks) (O:osabst) (t:tid)
                      (cst:clientst)
                      p (C:code) ke ks s pc A B sd,
                 p = (pc,(A,B,sd)) ->
                 get T t = Some C ->
                 C = (curs (hapi_code (spec_seq sched s)), (ke,ks)) ->
                 get O curtid = Some (oscurt t) ->
                 (~ exists t', sd O t') ->
                 hpstepabt p T cst O.

Inductive hpstepstar: hprog -> tasks -> clientst -> osabst  ->  
                      tasks -> clientst -> osabst  -> Prop:=
| hp_stepO: forall (p:hprog) (T:tasks) (cst:clientst) O,
              hpstepstar p T cst O  T cst O 
| hp_stepS: forall p T T' T'' cst cst' cst'' O O' O'',
              hpstep p T cst O T' cst' O' ->
              hpstepstar p T' cst' O'  T'' cst'' O''->
              hpstepstar p T cst O T'' cst'' O'' .

Inductive hpstepevstar: hprog -> tasks -> clientst -> osabst  ->  
                        tasks -> clientst -> osabst  -> val -> Prop:=
| hp_stepev: forall p T T' T'' T'''  cst cst' cst''  O O' O'' ev,
               hpstepstar p T cst O  T' cst' O' ->
               hpstepev p T' cst' O'  T'' cst' O'  ev->
               hpstepstar p T'' cst' O'  T''' cst'' O''->
               hpstepevstar p T cst O  T''' cst'' O'' ev.

Inductive hpstepabtstar: hprog -> tasks -> clientst -> osabst -> Prop:=
| hp_stepstarabt: forall p T cst O ,
                    (exists T' cst' O' , hpstepstar p T cst O  T' cst' O' /\
                                         hpstepabt p T' cst' O') -> hpstepabtstar p T cst O.

