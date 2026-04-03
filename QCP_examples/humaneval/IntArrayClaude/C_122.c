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

/*@ Extern Coq (sum_two_digit_upto: Z -> list Z -> Z)
               (sum_two_digit: Z -> list Z -> Z) */

int add_elements(int *arr, int arr_size, int k)
/*@ With lv
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        0 <= k && k <= arr_size &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        __return == sum_two_digit(k, lv) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv
        0 <= i && i <= k@pre &&
        s == sum_two_digit_upto(i, lv) &&
        IntArray::full(arr, arr_size@pre, lv)
    */
    for (i = 0; i < k; i++)
        if (arr[i] >= -99 && arr[i] <= 99)
            s += arr[i];
    return s;
}
