/*
Given a non-empty vector of integers arr && an integer k, return
the sum of the elements with at most two digits (in [-99, 99]) from the first k elements.

Example:
    Input: arr = {111,21,3,4000,5,6,7,8,9}, k = 4
    Output: 24   (21 + 3)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_122_pre_z: list Z -> Z -> Prop)
               (problem_122_spec_z: list Z -> Z -> Z -> Prop)
               (sum_two_digit_upto: Z -> list Z -> Z)
               (sum_two_digit_int_range: Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_122 */

int add_elements(int *arr, int arr_size, int k)
/*@ With lv
    Require
        1 <= arr_size && arr_size < INT_MAX &&
        1 <= k && k <= arr_size &&
        arr_size == Zlength(lv) &&
        problem_122_pre_z(lv, k) &&
        sum_two_digit_int_range(k, lv) &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        problem_122_spec_z(lv, k, __return) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        1 <= arr_size && arr_size < INT_MAX &&
        1 <= k && k <= arr_size &&
        arr_size == Zlength(lv) &&
        problem_122_pre_z(lv, k) &&
        sum_two_digit_int_range(k, lv) &&
        0 <= i && i <= k &&
        s == sum_two_digit_upto(i, lv) &&
        IntArray::full(arr, arr_size, lv)
    */
    for (i = 0; i < k; i++)
        if (arr[i] >= -99 && arr[i] <= 99)
            s += arr[i];
    return s;
}
