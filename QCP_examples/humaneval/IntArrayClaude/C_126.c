/*
Given a vector of numbers, return whether || ! they are sorted
in ascending order. If vector has more than 1 duplicate of the same
number, return false. Assume no negative numbers && only integers.

Examples
is_sorted({5}) ➞ true
is_sorted({1, 2, 3, 4, 5}) ➞ true
is_sorted({1, 3, 2, 4, 5}) ➞ false
is_sorted({1, 2, 3, 4, 5, 6}) ➞ true
is_sorted({1, 2, 3, 4, 5, 6, 7}) ➞ true
is_sorted({1, 3, 2, 4, 5, 6, 7}) ➞ false
is_sorted({1, 2, 2, 3, 3, 4}) ➞ true
is_sorted({1, 2, 2, 2, 3, 4}) ➞ false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_126_pre_z: list Z -> Prop)
               (problem_126_spec_z: list Z -> bool -> Prop)
               (sorted_no_triple_prefix: Z -> list Z -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import coins_126 */

int is_sorted(int* lst, int lst_size)
/*@ With lv
    Require
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_126_pre_z(lv) &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        ((__return != 0) && problem_126_spec_z(lv, true) ||
         (__return == 0) && problem_126_spec_z(lv, false)) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_126_pre_z(lv) &&
        1 <= i && i <= lst_size &&
        sorted_no_triple_prefix(i, lv) &&
        IntArray::full(lst, lst_size, lv)
    */
    for (int i=1;i<lst_size;i++)
    {
        if (lst[i]<lst[i-1]) return 0;
        if (i>=2 && lst[i]==lst[i-1] && lst[i]==lst[i-2]) return 0;
    }
    return 1;
}
