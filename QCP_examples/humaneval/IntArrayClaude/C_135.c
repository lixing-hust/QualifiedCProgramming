/*
Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
can_arrange({1,2,4,3,5}) = 3
can_arrange({1,2,3}) = -1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_135_pre_z: list Z -> Prop)
               (problem_135_spec_z: list Z -> Z -> Prop)
               (can_arrange_prefix: Z -> list Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_135 */

int can_arrange(int* arr, int arr_size)
/*@ With input_l
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_135_pre_z(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        problem_135_spec_z(input_l, __return) &&
        IntArray::full(arr, arr_size, input_l)
*/
{
    int max = -1;
    int i;
    /*@ Inv Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_135_pre_z(input_l) &&
        0 <= i && i <= arr_size &&
        can_arrange_prefix(i, input_l, max) &&
        IntArray::full(arr, arr_size, input_l)
    */
    for (i = 0; i < arr_size; i++)
        if (arr[i] <= i) max = i;
    return max;
}
