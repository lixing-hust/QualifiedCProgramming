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

/*@ Extern Coq (count_half_mismatches_upto: Z -> list Z -> Z)
               (count_half_mismatches: list Z -> Z) */

int smallest_change(int *arr, int arr_size)
/*@ With lv
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        __return == count_half_mismatches(lv) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int out = 0;
    int i;
    /*@ Inv
        0 <= i && 2 * i <= arr_size@pre &&
        out == count_half_mismatches_upto(i, lv) &&
        IntArray::full(arr, arr_size@pre, lv)
    */
    for (i = 0; i < arr_size - 1 - i; i++)
        if (arr[i] != arr[arr_size - 1 - i])
            out += 1;
    return out;
}
