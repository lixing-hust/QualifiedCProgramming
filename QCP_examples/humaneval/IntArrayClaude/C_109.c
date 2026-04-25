/*
Determine if a vector can be sorted in non-decreasing order by right-shift rotations.
This is true iff the number of "cyclic descents" (including wrap-around) is < 2.
Requires non-empty input.

move_one_ball({3, 4, 5, 1, 2}) ==> 1
move_one_ball({3, 5, 4, 1, 2}) ==> 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_109_pre_z: list Z -> Prop)
               (problem_109_spec_z: list Z -> Z -> Prop)
               (count_descents_prefix: Z -> list Z -> Z)
               (cyclic_descents: list Z -> Z)
               (descents_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_109 */

int move_one_ball(int *arr, int arr_size)
/*@ With input_l
    Require
        1 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_109_pre_z(input_l) &&
        descents_int_range(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        problem_109_spec_z(input_l, __return) &&
        IntArray::full(arr, arr_size, input_l)
*/
{
    int num = 0;
    int i;

    /*@ Inv Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        1 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_109_pre_z(input_l) &&
        descents_int_range(input_l) &&
        1 <= i && i <= arr_size &&
        num == count_descents_prefix(i, input_l) &&
        IntArray::full(arr, arr_size, input_l)
    */
    for (i = 1; i < arr_size; i++)
        if (arr[i] < arr[i - 1]) num += 1;
    if (arr[arr_size - 1] > arr[0]) num += 1;
    if (num < 2) return 1;
    return 0;
}
