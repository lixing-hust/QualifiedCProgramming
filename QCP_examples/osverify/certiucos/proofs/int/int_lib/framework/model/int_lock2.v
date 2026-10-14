Require Import memory2.
Require Import language2.

Definition picMin : int := Int.repr 3.     
Definition picMax : int := Int.repr 16. 
Definition levelMin : int := Int.repr 15.     (*0x000f*)
Definition levelMax : int := Int.repr 65521.  (*0xfff1 = 65521*)


Definition int_lock_aop (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
          exists er,
          vl = nil /\
          opv = None /\
          get O1 ierid = Some (hier er) /\
          O2 = set O1 ierid (hier (empupd er))
  end.

Definition int_unlock_aop (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
match rst with
    | (opv, O2) =>
        exists v er,
        vl = ((Vint32 v) :: nil) /\ 
        (Int.ltu levelMin v = true) /\ (Int.ltu v levelMax = true) /\
        get O1 ierid = Some (hier er) /\
        opv = None /\ O2 = set O1 ierid (hier (ierupds er (Int.unsigned v)))
end.

Definition int_disable_pic_aop (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
  match rst with
    | (opv, O2) =>
        exists v er,
          vl = ((Vint32 v) :: nil) /\ 
          (Int.ltu picMin v = true) /\ (Int.ltu v picMax = true) /\
          get O1 ierid = Some (hier er) /\
          opv = None /\ O2 = set O1 ierid (hier (ierupd er (Z.to_nat (Int.unsigned v)) false))
  end.

Definition int_enable_pic_aop (vl: vallist) (O1 : osabst) (rst : option val * osabst):=
match rst with
    | (opv, O2) =>
        exists v er,
        vl = ((Vint32 v) :: nil) /\ 
        (Int.ltu picMin v = true) /\ (Int.ltu v picMax = true) /\
        get O1 ierid = Some (hier er) /\
        opv = None /\ O2 = set O1 ierid (hier (ierupd er (Z.to_nat (Int.unsigned v)) true))
end.


