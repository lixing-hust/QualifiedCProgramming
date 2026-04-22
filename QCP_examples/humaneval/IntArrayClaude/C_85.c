/*
Given a non-empty vector of integers lst. add the even elements that are at odd indices.

Examples:
    add({4, 2, 6, 7}) ==> 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_85_pre_z: list Z -> Prop)
               (problem_85_spec_z: list Z -> Z -> Prop)
               (sum_even_at_odd_upto: Z -> list Z -> Z)
               (add_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_85 */


int add(int *lst, int lst_size)
/*@ With lv
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_85_pre_z(lv) &&
        add_int_range(lv) &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        problem_85_spec_z(lv, __return) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int s = 0;
    int i;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        0 <= i &&
        2 * i <= lst_size &&
        s == sum_even_at_odd_upto(i, lv) &&
        add_int_range(lv) &&
        IntArray::full(lst, lst_size, lv)
    */
    for (i = 0; i * 2 + 1 < lst_size; i++)
        if (lst[i * 2 + 1] % 2 == 0) s += lst[i * 2 + 1];
    return s;
}
