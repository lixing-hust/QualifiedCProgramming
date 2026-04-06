(*  Filter an input list of strings only for ones that start with a given prefix.
>>> filter_by_prefix([], 'a')
[]
>>> filter_by_prefix(['abc', 'bcd', 'cde', 'array'], 'a')
['abc', 'array'] *)

(* Spec(input : list string, substring : string, output list string) :=

​	∀s ∈ output, s  ∈ input /\
​	∀s ∈ output, prefix(substring, s) /\
​	∀s ∈ input, prefix(substring, s) → s ∈ output /\
​	∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(*
  子列表定义
*)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.


(* Pre: no additional constraints for `filter_by_prefix` by default *)
Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  (* 1. output 是 input 的一个子序列。
        这个自定义的 is_subsequence 保证了：
        - output 中的所有元素都来自 input (规约第一条)
        - output 中元素的相对顺序与 input 中一致 (规约第四条)
  *)
  is_subsequence output input /\

  (* 2. 一个字符串 s 在 output 中，当且仅当它在 input 中且满足前缀条件。
        这蕴含了：
        - output 中的所有元素都满足前缀条件 (规约第二条)
        - input 中所有满足前缀条件的元素都在 output 中 (规约第三条)
  *)
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).
