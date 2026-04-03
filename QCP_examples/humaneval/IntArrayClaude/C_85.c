/*
Given a non-empty vector of integers lst. add the even elements that are at odd indices.

Examples:
    add({4, 2, 6, 7}) ==> 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (sum_even_at_odd: list Z -> Z)
               (sum_even_at_odd_upto: Z -> list Z -> Z) */

int add(int *lst, int lst_size)
/*@ With lv
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        __return == sum_even_at_odd(lv) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv
        0 <= i && 2 * i <= lst_size@pre &&
        s == sum_even_at_odd_upto(i, lv) &&
        IntArray::full(lst, lst_size@pre, lv)
    */
    for (i = 0; i * 2 + 1 < lst_size; i++)
        if (lst[i * 2 + 1] % 2 == 0) s += lst[i * 2 + 1];
    return s;
}
