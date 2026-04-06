(* def bf(planet1, planet2):
'''
There are eight planets in our solar system: the closerst to the Sun
is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn,
Uranus, Neptune.
Write a function that takes two planet names as strings planet1 and planet2.
The function should return a tuple containing all planets whose orbits are
located between the orbit of planet1 and the orbit of planet2, sorted by
the proximity to the sun.
The function should return an empty tuple if planet1 or planet2
are not correct planet names.
Examples
bf("Jupiter", "Neptune") ==> ("Saturn", "Uranus")
bf("Earth", "Mercury") ==> ("Venus")
bf("Mercury", "Uranus") ==> ("Venus", "Earth", "Mars", "Jupiter", "Saturn")
''' *)
(* 引入必要的 Coq 库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

(* 定义行星名称为 string，并按与太阳的距离排序 *)
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition solar_system : list string :=
  [ "Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune" ].


(* 辅助函数：获取一个行星在 solar_system 列表中的索引 (位置)。
   不使用递归实现，而是用 fold_left 从左到右遍历并记录索引。
   累加器是 (current_index, found_option)，当找到匹配时记录当前位置。 *)
Definition get_planet_index (p_name : string) : option nat :=
  snd (
    fold_left (fun acc p =>
      let '(i, res) := acc in
      match res with
      | Some _ => (S i, res)
      | None => if String.eqb p p_name then (S i, Some i) else (S i, None)
      end) solar_system (0, None)).

(*
  bf 函数的程序规约 (Spec)
  - 输入: planet1 (list ascii), planet2 (list ascii)
  - 输出: result (list (list ascii))
*)
(* 独立的输入前置条件 *)
Definition problem_148_pre (planet1 planet2 : string) : Prop := True.

Definition problem_148_spec (planet1 planet2 : string) (result : list string) : Prop :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    (* --- 情况 1: planet1 和 planet2 都是有效的行星名称 --- *)
    let min_idx := min idx1 idx2 in
    let max_idx := max idx1 idx2 in
    
    (* 属性 1: 输出列表 `result` 中的每个行星 `p`，当且仅当 `p` 的轨道
       位置在 `planet1` 和 `planet2` 的轨道之间。*)
    (forall p, In p result <->
      (exists idx, get_planet_index p = Some idx /\
                   min_idx < idx < max_idx))
    /\
    (* 属性 2: 输出列表 `result` 必须是根据与太阳的距离排序的。*)
    (forall p_a p_b i j,
      nth_error result i = Some p_a ->
      nth_error result j = Some p_b ->
      i < j ->
      (exists idx_a idx_b,
         get_planet_index p_a = Some idx_a /\
         get_planet_index p_b = Some idx_b /\
         idx_a < idx_b))

  | _, _ =>
    (* --- 情况 2: planet1 或 planet2 不是有效的行星名称 --- *)
    (* 输出 `result` 必须为空列表。*)
    result = []
  end.