/*
Given a vector arr of integers, find the minimum number of elements that
need to be changed to make the vector palindromic. A palindromic vector is a vector that
is read the same backwards && forwards. In one change, you can change one element to any other element.

For example:
smallest_change({1,2,3,5,4,7,9,6}) == 4
smallest_change({1, 2, 3, 4, 3, 2, 2}) == 1
smallest_change({1, 2, 3, 2, 1}) == 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_73_pre_z: list Z -> Prop)
               (problem_73_spec_z: list Z -> Z -> Prop)
               (count_half_mismatches_upto: Z -> list Z -> Z)
               (smallest_change_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_73 */

int smallest_change(int *arr, int arr_size)
/*@ With lv
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(lv) &&
        problem_73_pre_z(lv) &&
        smallest_change_int_range(lv) &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        problem_73_spec_z(lv, __return) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int out = 0;
    int i;

    /*@ Inv Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(lv) &&
        problem_73_pre_z(lv) &&
        smallest_change_int_range(lv) &&
        0 <= i &&
        2 * i <= arr_size &&
        out == count_half_mismatches_upto(i, lv) &&
        IntArray::full(arr, arr_size, lv)
    */
    for (i = 0; i < arr_size - 1 - i; i++)
        if (arr[i] != arr[arr_size - 1 - i])
            out += 1;
    return out;
}
