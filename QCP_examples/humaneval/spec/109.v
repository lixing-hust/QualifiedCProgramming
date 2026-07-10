(* We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The
numbers in the array will be randomly ordered. Your task is to determine if
it is possible to get an array sorted in non-decreasing order by performing
the following operation on the given array:
You are allowed to perform right shift operation any number of times.

One right shift operation means shifting all elements of the array by one
position in the right direction. The last element of the array will be moved to
the starting position in the array i.e. 0th index.

If it is possible to obtain the sorted array by performing the above operation
then return True else return False.
If the given array is empty then return True.

Note: The given list is guaranteed to have unique elements.

For Example:

move_one_ball([3, 4, 5, 1, 2])==>True
Explanation: By performin 2 right shift operations, non-decreasing order can
be achieved for the given array.
move_one_ball([3, 5, 4, 1, 2])==>False
Explanation:It is not possible to get non-decreasing order for the given
array by performing any number of right shift operations. *)

(* 导入列表、整数和自然数所需的基础库 *)
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.


(* sorted_list states non-decreasing order over integers. *)
Definition sorted_list (l : list Z) : Prop :=
  Sorted Z.le l.

(* right_shift moves the last element to the front, preserving empty lists. *)
Definition right_shift (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | hd :: tl => hd :: rev tl
  end.

(* rotation_sorted says that some cyclic rotation of arr is sorted. *)
Definition rotation_sorted (arr : list Z) : Prop :=
  exists prefix suffix,
    arr = prefix ++ suffix /\
    sorted_list (suffix ++ prefix).

(* problem_109_pre requires unique elements, matching the task statement. *)
Definition problem_109_pre (arr : list Z) : Prop := NoDup arr.

(* problem_109_spec relates the boolean result to the existence of a sorted rotation. *)
Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> rotation_sorted arr.
