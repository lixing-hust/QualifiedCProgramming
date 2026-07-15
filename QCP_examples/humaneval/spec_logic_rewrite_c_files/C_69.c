/*
You are given a non-empty vector of positive integers. Return the greatest integer that is greater than
zero, && has a frequency greater than || equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the vector.
If no such a value exist, return -1.
Examples:
    search({4, 1, 2, 2, 3, 1}) == 2
    search({1, 2, 2, 3, 3, 3, 4, 4, 4}) == 3
    search({5, 5, 4, 4, 4}) == -1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_69_pre_z: list Z -> Prop)
               (problem_69_spec_z: list Z -> Z -> Prop)
               (count_prefix_69: Z -> Z -> list Z -> Z)
               (count_z_69: Z -> list Z -> Z)
               (find_max_prefix_69: list Z -> Z -> Z)
               (update_best_69: Z -> Z -> Z -> Z)
               (list_positive_int_range_69: list Z -> Prop) */
/*@ Import Coq Require Import coins_69 */

int search(int* lst, int lst_size)
/*@ With input_l
    Require
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_69_pre_z(input_l) &&
        list_positive_int_range_69(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_69_spec_z(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int max = -1;
    int i;
    int x;
    int freq;
    int j;
    int old_max;
    x = 0;
    freq = 0;
    j = 0;
    old_max = -1;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_69_pre_z(input_l) &&
        list_positive_int_range_69(input_l) &&
        0 <= i && i <= lst_size &&
        -1 <= max && max <= INT_MAX &&
        max == find_max_prefix_69(input_l, i) &&
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= freq && freq <= INT_MAX &&
        INT_MIN <= j && j <= INT_MAX &&
        INT_MIN <= old_max && old_max <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i = 0; i < lst_size; i++) {
        x = lst[i];
        freq = 0;

        /*@ Inv Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            1 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre_z(input_l) &&
            list_positive_int_range_69(input_l) &&
            0 <= i && i < lst_size &&
            x == Znth(i, input_l, 0) &&
            1 <= x && x <= INT_MAX &&
            0 <= j && j <= lst_size &&
            0 <= freq && freq <= j &&
            freq == count_prefix_69(x, j, input_l) &&
            -1 <= max && max <= INT_MAX &&
            max == find_max_prefix_69(input_l, i) &&
            INT_MIN <= old_max && old_max <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
        for (j = 0; j < lst_size; j++) {
            if (lst[j] == x) {
                freq += 1;
            }
        }

        old_max = max;
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            1 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre_z(input_l) &&
            list_positive_int_range_69(input_l) &&
            0 <= i && i < lst_size &&
            x == Znth(i, input_l, 0) &&
            1 <= x && x <= INT_MAX &&
            freq == count_z_69(x, input_l) &&
            max == old_max &&
            old_max == find_max_prefix_69(input_l, i) &&
            -1 <= old_max && old_max <= INT_MAX &&
            INT_MIN <= x && x <= INT_MAX &&
            INT_MIN <= freq && freq <= INT_MAX &&
            INT_MIN <= j && j <= INT_MAX &&
            INT_MIN <= old_max && old_max <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
        if (freq >= x) {
            if (x > old_max) {
                max = x;
            }
        }
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            1 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre_z(input_l) &&
            list_positive_int_range_69(input_l) &&
            0 <= i && i < lst_size &&
            x == Znth(i, input_l, 0) &&
            freq == count_z_69(x, input_l) &&
            old_max == find_max_prefix_69(input_l, i) &&
            max == update_best_69(old_max, x, freq) &&
            -1 <= max && max <= INT_MAX &&
            max == find_max_prefix_69(input_l, i + 1) &&
            INT_MIN <= x && x <= INT_MAX &&
            INT_MIN <= freq && freq <= INT_MAX &&
            INT_MIN <= j && j <= INT_MAX &&
            INT_MIN <= old_max && old_max <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }
    return max;
}
