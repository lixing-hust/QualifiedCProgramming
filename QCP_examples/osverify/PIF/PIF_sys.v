(* Require Import oscorrectness.  *)
Require Import PIF_os_mutex_cap.
Require Import PIF_spec.
Require Import PIF_os_code_defs.
Require Import PIF_os_ucos_h.
Require Import PIF_code_notations.


Definition api_spec_list' := 
  (pthread_mutex_unlock, mutexunlockapi) ::
  (pthread_mutex_lock, mutexlockapi) ::
  (pthread_mutex_timedlock, mutextimedlockapi) ::
  (pthread_mutex_trylock, mutextrylockapi) ::
  (pthread_mutex_init, mutexinitapi) ::
  (pthread_mutex_destroy, pthread_mutex_destroy_api) ::
  (pthread_mutexattr_init, mutexattrinitapi) :: 
  (pthread_mutexattr_destroy, mutexattrdestroyapi) :: 
  (pthread_mutexattr_settype, mutexattrsettypeapi) :: 
  (pthread_mutexattr_gettype, mutexattrgettypeapi) :: 
  (pthread_mutexattr_setprioceiling, mutexattrsetprioceilingapi) :: 
  (pthread_mutexattr_getprioceiling, mutexattrgetprioceilingapi) :: 
  nil.

Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Definition api_spec':= convert_api_spec api_spec_list'.

Definition int_spec_list' : list (hid * int_code) := nil .

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.
Definition int_spec'  := convert_int_spec int_spec_list'.
Definition os_spec' := (api_spec',int_spec',GetHPrio).
