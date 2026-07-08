(* def do_algebra(operator, operand):
"""
Given two lists operator, and operand. The first list has basic algebra operations, and
the second list is a list of integers. Use the two given lists to build the algebric
expression and return the evaluation of this expression.

The basic algebra operations:
Addition ( + )
Subtraction ( - )
Multiplication ( * )
Floor division ( // )
Exponentiation ( ** )

Example:
operator['+', '*', '-']
array = [2, 3, 4, 5]
result = 2 + 3 * 4 - 5
=> result = 9

Note:
The length of operator list is equal to the length of operand list minus one.
Operand is a list of of non-negative integers.
Operator list has at least one operator, and operand list has at least two operands.

""" *)
(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.


(* 此函数将字符形式的运算符解释为对应的二元整数运算。*)
Definition interp_op (op : ascii) : (Z -> Z -> Z) :=
  match op with
  | "+"%char => Z.add
  | "-"%char => Z.sub
  | "*"%char => Z.mul
  | "/"%char => Z.div
  | "^"%char => Z.pow
  | _ => fun _ _ => 0
  end.

Definition eval (ops : list ascii) (nums : list Z) : Z :=
  let prec := fun op =>
    match op with
    | "+"%char | "-"%char => 0%nat
    | "*"%char | "/"%char => 1%nat
    | "^"%char => 2%nat
    | _ => 0%nat
    end in
  let should_reduce := fun incoming top =>
    orb (Nat.ltb (prec incoming) (prec top))
        (andb (Nat.eqb (prec incoming) (prec top))
              (negb (incoming =? "^"%char)%char)) in
  let apply_top : (list Z * list ascii)%type -> (list Z * list ascii)%type :=
    fun st =>
      match st with
      | (rhs :: lhs :: values, op :: rest_ops) =>
          (interp_op op lhs rhs :: values, rest_ops)
      | _ => st
      end in
  let reduce_before : ascii -> (list Z * list ascii)%type -> (list Z * list ascii)%type :=
    fun incoming st =>
      Nat.iter (List.length (snd st))
        (fun st' =>
           match snd st' with
           | top :: _ => if should_reduce incoming top then apply_top st' else st'
           | [] => st'
           end)
        st in
  let push : (list Z * list ascii)%type -> (ascii * Z)%type -> (list Z * list ascii)%type :=
    fun st item =>
      let '(op, rhs) := item in
      let st' := reduce_before op st in
      (rhs :: fst st', op :: snd st') in
  let st := fold_left push (combine ops (tl nums)) ([hd 0 nums], []) in
  match fst (Nat.iter (List.length (snd st)) apply_top st) with
  | result :: _ => result
  | [] => 0
  end.

Definition do_algebra_impl (operators : string) (operands : list Z) : Z :=
  eval (list_ascii_of_string operators) operands.

(* 约束：
   - 操作符长度 = 操作数长度 - 1，且操作符至少1个、操作数至少2个
   - 操作数非负
   - 操作符仅限于 + - * / ^
*)
Definition problem_160_pre (operators : string) (operands : list Z) : Prop :=
  let ops := list_ascii_of_string operators in
  S (List.length ops) = List.length operands /\
  (1 <= List.length ops)%nat /\ (2 <= List.length operands)%nat /\
  Forall (fun z => 0 <= z) operands /\
  Forall (fun c => c = "+"%char \/ c = "-"%char \/ c = "*"%char \/ c = "/"%char \/ c = "^"%char) ops.

Definition problem_160_spec (operators : string) (operands : list Z) (result : Z) : Prop :=
  result = do_algebra_impl operators operands.
