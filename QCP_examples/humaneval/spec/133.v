(* def sum_squares(lst):
You are given a list of numbers.
You need to return the sum of squared numbers in the given list,
round each element in the list to the upper int(Ceiling) first.
Examples:
For lst = [1,2,3] the output should be 14
For lst = [1,4,9] the output should be 98
For lst = [1,3,5,7] the output should be 84
For lst = [1.4,4.2,0] the output should be 29
For lst = [-2.4,1,1] the output should be 6 *)
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.
(* z 是 x 的 ceiling 的一个等价刻画： IZR z - 1 < x <= IZR z *)
Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

(* 任意实数列表均可 *)
Definition problem_133_pre (lst : list R) : Prop := True.

(* 规约：对于输入实数列表 lst，输出 s 为对应每个元素向上取整后的整数的平方和 *)
Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).
