(* This function takes two positive numbers x and y and returns the
biggest even integer number that is in the range [x, y] inclusive. If
there's no such number, then the function should return -1.

For example:
choose_num(12, 15) = 14
choose_num(13, 12) = -1 *)

(* 导入 Coq 的整数库 ZArith *)
Require Import Coq.ZArith.ZArith.

(* 打开 Z 的作用域，这样就可以直接使用像 +, -, <= 等符号，而不用写 Z.add, Z.sub, Z.le *)
Open Scope Z_scope.

(* x 与 y 均为正整数 *)
Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

(* 
   定义 choose_num 函数的规约 (Specification)
   它描述了输入 x, y 和输出 res 之间必须满足的关系。
*)
Definition problem_102_spec (x y res : Z) : Prop :=

  (* 情况一：当区间 [x, y] 中存在偶数时 *)
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须是这个区间内最大的偶数 *)
    (Z.even res = true/\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y ->  Z.even z' = false)) )
  /\
  (* 情况二：当区间 [x, y] 中不存在偶数时 *)
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须等于 -1 *)
    res = -1 ).