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

/*@ Extern Coq (problem_121_pre_z: list Z -> Prop)
               (problem_121_spec_z: list Z -> Z -> Prop)
               (sum_odd_at_even_upto: Z -> list Z -> Z)
               (sum_odd_at_even_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_121 */

int solutions(int *lst, int lst_size)
/*@ With lv
    Require
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_121_pre_z(lv) &&
        sum_odd_at_even_int_range(lv) &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        problem_121_spec_z(lv, __return) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_121_pre_z(lv) &&
        sum_odd_at_even_int_range(lv) &&
        0 <= i && 2 * i <= lst_size + 1 &&
        s == sum_odd_at_even_upto(i, lv) &&
        IntArray::full(lst, lst_size, lv)
    */
    for (i = 0; i * 2 < lst_size; i++)
        if (lst[i * 2] % 2 == 1) s += lst[i * 2];
    return s;
}
