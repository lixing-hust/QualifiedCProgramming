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

/*@ Extern Coq (count_descents_prefix: Z -> list Z -> Z)
               (cyclic_descents: list Z -> Z) */

int move_one_ball(int *arr, int arr_size)
/*@ With lv
    Require
        1 <= arr_size && arr_size < INT_MAX &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        ((__return != 0) && cyclic_descents(lv) < 2 ||
         (__return == 0) && cyclic_descents(lv) >= 2) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int num = 0;
    int i;
    /*@ Inv
        1 <= i && i <= arr_size@pre &&
        num == count_descents_prefix(i, lv) &&
        IntArray::full(arr, arr_size@pre, lv)
    */
    for (i = 1; i < arr_size; i++)
        if (arr[i] < arr[i - 1]) num += 1;
    if (arr[arr_size - 1] > arr[0]) num += 1;
    if (num < 2) return 1;
    return 0;
}
