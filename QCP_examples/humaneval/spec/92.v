(* def any_int(x, y, z):
'''
Create a function that takes 3 numbers.
Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers.
Returns false in any other cases.

Examples
any_int(5, 2, 7) ➞ True

any_int(3, 2, 2) ➞ False

any_int(3, -2, 1) ➞ True

any_int(3.6, -2.2, 2) ➞ False



''' *)
(* Import Coq's libraries for Rational Numbers and Integers *)
Require Import QArith ZArith.
Open Scope Q_scope.
Open Scope Z_scope.

(* 任意三个有理数输入均可，无附加约束 *)
Definition problem_92_pre (x y z : Q) : Prop := True.

(*
  any_int_spec is the program specification for the any_int function.
  It describes the relationship between the inputs x, y, z and the output b.
  - x, y, z : Q      Program inputs, using rational numbers to handle all cases.
  - b : bool         Program output, a boolean value.
*)
Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (*
      The entire condition is expressed with an existential quantifier.
      This reads: "There exist integers zx, zy, and zz such that..."
    *)
    (exists zx zy zz : Z,
      (* Condition 1: ...x, y, and z are equal to those integers
         (represented as rationals). This is the correct way to assert
         that x, y, and z are all integers. *)
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\

      (* Condition 2: ...and those integers satisfy the summation property. *)
      (zx = zy + zz \/
       zy = zx + zz \/
       zz = zx + zy)).