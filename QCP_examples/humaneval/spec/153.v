(* def Strongest_Extension(class_name, extensions):
"""You will be given the name of a class (a string) and a list of extensions.
The extensions are to be used to load additional classes to the class. The
strength of the extension is as follows: Let CAP be the number of the uppercase
letters in the extension's name, and let SM be the number of lowercase letters
in the extension's name, the strength is given by the fraction CAP - SM.
You should find the strongest extension and return a string in this
format: ClassName.StrongestExtensionName.
If there are two or more extensions with the same strength, you should
choose the one that comes first in the list.
For example, if you are given "Slices" as the class and a list of the
extensions: ['SErviNGSliCes', 'Cheese', 'StuFfed'] then you should
return 'Slices.SErviNGSliCes' since 'SErviNGSliCes' is the strongest extension
(its strength is -1).
Example:
for Strongest_Extension('my_class', ['AA', 'Be', 'CC']) == 'my_class.AA'
""" *)
(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* 定义：检查一个字符是否为大写字母 *)
Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

(* 定义：检查一个字符是否为小写字母 *)
Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

(* 辅助函数：计算列表中满足特定谓词的字符数量 *)
Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

(* 定义：计算一个扩展名的“力量值” *)
Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

(*
  谓词：is_strongest best exts
  该谓词为真，当且仅当 'best' 是列表 'exts' 中的最强扩展。
  这一定义蕴含了当力量值相同时，选择最先出现的扩展的规则。
*)
Definition is_strongest (best : string) (exts : list string) : Prop :=
  (* 我们可以将列表 'exts' 在 'best' 第一次出现的位置拆分为 'prefix' 和 'post' *)
  exists prefix post,
    exts = prefix ++ best :: post /\
    ~ In best prefix /\ (* 确保这是 'best' 第一次出现 *)
    (
      (* 'best' 的力量值必须严格大于它前面所有元素的力量值 *)
      (forall e, In e prefix -> (strength e < strength best)%Z) /\
      (* 'best' 的力量值必须大于或等于它后面所有元素的力量值 *)
      (forall e, In e post -> (strength e <= strength best)%Z)
    ).

(* 扩展列表必须非空 *)
Definition problem_153_pre (class_name : string) (extensions : list string) : Prop :=
  extensions <> [].


(*
  程序规约：Spec class_name extensions res
  它定义了输入 class_name 和 extensions 与输出 res 之间的关系。
*)
Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False (* 对于空的扩展列表，行为是未定义的，因此规约为假 *)
  | _ :: _ => (* 对于非空的扩展列表 *)
      (* 必须存在一个最强的扩展名 'strongest_ext' *)
      exists strongest_ext,
        is_strongest strongest_ext extensions /\
        (* 并且输出 'res' 是 class_name, '.', 和 strongest_ext 的拼接 *)
        res = class_name ++ "." %string ++ strongest_ext
  end.