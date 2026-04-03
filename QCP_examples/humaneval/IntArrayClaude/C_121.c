/*
Given a non-empty vector of integers, return the sum of all of the odd elements
that are in even positions (0-indexed).

Examples:
solution({5, 8, 7, 1}) ==> 12   (5 + 7)
solution({3, 3, 3, 3, 3}) ==> 9
solution({30, 13, 24, 321}) ==> 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (sum_odd_at_even: list Z -> Z)
               (sum_odd_at_even_upto: Z -> list Z -> Z) */

int solutions(int *lst, int lst_size)
/*@ With lv
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        __return == sum_odd_at_even(lv) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv
        0 <= i && 2 * i <= lst_size@pre &&
        s == sum_odd_at_even_upto(i, lv) &&
        IntArray::full(lst, lst_size@pre, lv)
    */
    for (i = 0; i * 2 < lst_size; i++)
        if (lst[i * 2] % 2 == 1) s += lst[i * 2];
    return s;
}
