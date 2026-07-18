(* def cycpattern_check(a , b):
"""You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => False
cycpattern_check("hello","ell") => True
cycpattern_check("whassup","psus") => False
cycpattern_check("abab","baa") => True
cycpattern_check("efef","eeff") => False
cycpattern_check("himenss","simen") => True

""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

(* is_substring states that sub appears contiguously inside main. *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* is_rotation_of states that r is a cyclic rotation of b. *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* problem_154_pre imposes no input constraints. *)
Definition problem_154_pre (a b : string) : Prop := True.

(* problem_154_spec follows the canonical program: the empty second word
   produces false; otherwise, res is true exactly when some rotation of b is
   a substring of a. *)
Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <->
    lb <> [] /\
    exists b', is_rotation_of b' lb /\ is_substring b' la.
