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

/*@ Extern Coq (problem_69_pre: list Z -> Prop)
               (problem_69_spec: list Z -> Z -> Prop)
               (search_int_range_69: list Z -> Prop)
               (search_outer_state_69: list Z -> Z -> list Z -> list Z -> Z -> Prop)
               (search_inner_state_69: list Z -> Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
               (search_inner_to_outer_69: list Z -> Z -> list Z -> list Z -> Z -> Z -> Prop)
               (search_after_val_write_69: list Z -> Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
               (search_outer_add_new_69: list Z -> Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_69 */

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int init_size, int size)
/*@ With l
    Require
        array != 0 &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        init_size == Zlength(l) &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure emp
*/;

int search(int* lst, int lst_size)
/*@ With input_l
    Require
        0 < lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_69_pre(input_l) &&
        search_int_range_69(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_69_spec(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int* vals;
    int* cnts;
    int freq_size = 0;
    int max = -1;

    vals = malloc_int_array(lst_size);
    cnts = malloc_int_array(lst_size);
    if (vals == 0 || cnts == 0) {
        return -1;
    }

    int i;
    int current = 0;
    int has = 0;
    int j = 0;
    /*@ Inv Assert
        exists vals_l cnts_l,
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        vals != 0 &&
        cnts != 0 &&
        0 < lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_69_pre(input_l) &&
        search_int_range_69(input_l) &&
        current == current &&
        has == has &&
        j == j &&
        0 <= i && i <= lst_size &&
        0 <= freq_size && freq_size <= i &&
        freq_size == Zlength(vals_l) &&
        freq_size == Zlength(cnts_l) &&
        -1 <= max && max < INT_MAX &&
        search_outer_state_69(input_l, i, vals_l, cnts_l, max) &&
        IntArray::full(lst, lst_size, input_l) *
        IntArray::seg(vals, 0, freq_size, vals_l) *
        IntArray::undef_seg(vals, freq_size, lst_size) *
        IntArray::seg(cnts, 0, freq_size, cnts_l) *
        IntArray::undef_seg(cnts, freq_size, lst_size)
    */
    for (i=0; i<lst_size; i++)
    {
        current = lst[i];
        has = 0;
        /*@ Inv Assert
            exists vals_l cnts_l,
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            vals != 0 &&
            cnts != 0 &&
            0 < lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre(input_l) &&
            search_int_range_69(input_l) &&
            current == Znth(i, input_l, 0) &&
            0 < current && current < INT_MAX &&
            0 <= i && i < lst_size &&
            0 <= j && j <= freq_size &&
            0 <= freq_size && freq_size <= i &&
            freq_size == Zlength(vals_l) &&
            freq_size == Zlength(cnts_l) &&
            has == 0 &&
            -1 <= max && max < INT_MAX &&
            search_inner_state_69(input_l, i, j, vals_l, cnts_l, has, max) &&
            IntArray::full(lst, lst_size, input_l) *
            IntArray::seg(vals, 0, freq_size, vals_l) *
            IntArray::undef_seg(vals, freq_size, lst_size) *
            IntArray::seg(cnts, 0, freq_size, cnts_l) *
            IntArray::undef_seg(cnts, freq_size, lst_size)
        */
        for (j=0; j<freq_size; j++)
            if (current==vals[j])
            {
                cnts[j]+=1;
                has=1;
                if (cnts[j]>=vals[j] && vals[j]>max) max=vals[j];
                break;
            }
        /*@ Assert
            exists vals_l cnts_l,
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            vals != 0 &&
            cnts != 0 &&
            0 < lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre(input_l) &&
            search_int_range_69(input_l) &&
            current == Znth(i, input_l, 0) &&
            0 < current && current < INT_MAX &&
            0 <= i && i < lst_size &&
            0 <= freq_size && freq_size <= i &&
            0 <= freq_size && freq_size < lst_size &&
            freq_size < lst_size &&
            j == j &&
            freq_size == Zlength(vals_l) &&
            freq_size == Zlength(cnts_l) &&
            (has == 0 || has == 1) &&
            -1 <= max && max < INT_MAX &&
            search_inner_to_outer_69(input_l, i, vals_l, cnts_l, has, max) &&
            IntArray::full(lst, lst_size, input_l) *
            IntArray::seg(vals, 0, freq_size, vals_l) *
            IntArray::undef_seg(vals, freq_size, lst_size) *
            IntArray::seg(cnts, 0, freq_size, cnts_l) *
            IntArray::undef_seg(cnts, freq_size, lst_size)
        */
        if (has == 0)
        {
            /*@ Assert
                exists vals_l cnts_l,
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                vals != 0 &&
                cnts != 0 &&
                0 < lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(input_l) &&
                problem_69_pre(input_l) &&
                search_int_range_69(input_l) &&
                current == Znth(i, input_l, 0) &&
                0 < current && current < INT_MAX &&
                0 <= i && i < lst_size &&
                0 <= freq_size && freq_size <= i &&
                0 <= freq_size && freq_size < lst_size &&
                j == j &&
                freq_size == Zlength(vals_l) &&
                freq_size == Zlength(cnts_l) &&
                has == 0 &&
                -1 <= max && max < INT_MAX &&
                search_inner_to_outer_69(input_l, i, vals_l, cnts_l, has, max) &&
                IntArray::full(lst, lst_size, input_l) *
                IntArray::seg(vals, 0, freq_size, vals_l) *
                IntArray::undef_seg(vals, freq_size, freq_size + 1) *
                IntArray::undef_seg(vals, freq_size + 1, lst_size) *
                IntArray::seg(cnts, 0, freq_size, cnts_l) *
                IntArray::undef_seg(cnts, freq_size, freq_size + 1) *
                IntArray::undef_seg(cnts, freq_size + 1, lst_size)
            */
            vals[freq_size]=current;
            /*@ Assert
                exists vals_l cnts_l,
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                vals != 0 &&
                cnts != 0 &&
                0 < lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(input_l) &&
                problem_69_pre(input_l) &&
                search_int_range_69(input_l) &&
                current == Znth(i, input_l, 0) &&
                0 < current && current < INT_MAX &&
                0 <= i && i < lst_size &&
                0 <= freq_size && freq_size <= i &&
                freq_size < lst_size &&
                j == j &&
                has == has &&
                freq_size + 1 == Zlength(vals_l) &&
                freq_size == Zlength(cnts_l) &&
                -1 <= max && max < INT_MAX &&
                search_after_val_write_69(input_l, i, vals_l, cnts_l, max, current, freq_size) &&
                IntArray::full(lst, lst_size, input_l) *
                IntArray::seg(vals, 0, freq_size + 1, vals_l) *
                IntArray::undef_seg(vals, freq_size + 1, lst_size) *
                IntArray::seg(cnts, 0, freq_size, cnts_l) *
                IntArray::undef_seg(cnts, freq_size, lst_size)
            */
            cnts[freq_size]=1;
            freq_size += 1;
            if (max==-1 && current==1) max=1;
            /*@ Assert
                exists vals_l cnts_l,
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                vals != 0 &&
                cnts != 0 &&
                0 < lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(input_l) &&
                problem_69_pre(input_l) &&
                search_int_range_69(input_l) &&
                current == Znth(i, input_l, 0) &&
                0 < current && current < INT_MAX &&
                0 <= i && i < lst_size &&
                0 <= freq_size && freq_size <= i + 1 &&
                j == j &&
                has == has &&
                freq_size == Zlength(vals_l) &&
                freq_size == Zlength(cnts_l) &&
                -1 <= max && max < INT_MAX &&
                search_outer_add_new_69(input_l, i, vals_l, cnts_l, max, Znth(i, input_l, 0), freq_size, 1) &&
                IntArray::full(lst, lst_size, input_l) *
                IntArray::seg(vals, 0, freq_size, vals_l) *
                IntArray::undef_seg(vals, freq_size, lst_size) *
                IntArray::seg(cnts, 0, freq_size, cnts_l) *
                IntArray::undef_seg(cnts, freq_size, lst_size)
            */
        }
        /*@ Assert
            exists vals_l cnts_l,
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            vals != 0 &&
            cnts != 0 &&
            0 < lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_69_pre(input_l) &&
            search_int_range_69(input_l) &&
            current == Znth(i, input_l, 0) &&
            0 < current && current < INT_MAX &&
            0 <= i && i < lst_size &&
            0 <= freq_size && freq_size <= i + 1 &&
            j == j &&
            has == has &&
            freq_size == Zlength(vals_l) &&
            freq_size == Zlength(cnts_l) &&
            -1 <= max && max < INT_MAX &&
            search_outer_state_69(input_l, i + 1, vals_l, cnts_l, max) &&
            IntArray::full(lst, lst_size, input_l) *
            IntArray::seg(vals, 0, freq_size, vals_l) *
            IntArray::undef_seg(vals, freq_size, lst_size) *
            IntArray::seg(cnts, 0, freq_size, cnts_l) *
            IntArray::undef_seg(cnts, freq_size, lst_size)
        */
    }
    free_int_array(vals, freq_size, lst_size);
    free_int_array(cnts, freq_size, lst_size);
    return max;
}
