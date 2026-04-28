/*
You are given a vector of integers.
Write a function next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

next_smallest({1, 2, 3, 4, 5}) == 2
next_smallest({5, 1, 4, 3, 2}) == 2
next_smallest({}) == None
next_smallest({1, 1}) == None
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_90_pre_z: list Z -> Prop)
               (problem_90_spec_z: list Z -> Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (no_distinct_prefix: Z -> list Z -> Prop)
               (next_smallest_sorted_bridge: list Z -> list Z -> Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_90 */

void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require
        array != 0 &&
        init_size == Zlength(l) &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        exists sorted_l sorted_full_l,
        init_size == Zlength(sorted_l) &&
        size == Zlength(sorted_full_l) &&
        sublist(0, init_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, sorted_full_l)
*/;

int next_smallest(int *lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        (lst_size > 1 => lst != 0) &&
        lst_size == Zlength(input_l) &&
        problem_90_pre_z(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        exists final_l,
        problem_90_spec_z(input_l, __return) &&
        lst_size == Zlength(final_l) &&
        IntArray::full(lst, lst_size, final_l)
*/
{
    int i;

    if (lst_size <= 1) {
        return -1;
    }

    /*@ Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        lst != 0 &&
        1 < lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_90_pre_z(input_l) &&
        undef_data_at(&i) *
        IntArray::seg(lst, 0, lst_size, input_l) *
        IntArray::undef_seg(lst, lst_size, lst_size)
    */
    sort_int_array(lst, lst_size, lst_size, 1);

    /*@ Inv Assert
        exists sorted_l,
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 < lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        lst_size == Zlength(sorted_l) &&
        problem_90_pre_z(input_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        next_smallest_sorted_bridge(input_l, sorted_l, lst_size) &&
        1 <= i && i <= lst_size &&
        no_distinct_prefix(i, sorted_l) &&
        IntArray::full(lst, lst_size, sorted_l)
    */
    for (i = 1; i < lst_size; i++) {
        if (lst[i] != lst[i - 1]) {
            return lst[i];
        }
    }
    return -1;
}
