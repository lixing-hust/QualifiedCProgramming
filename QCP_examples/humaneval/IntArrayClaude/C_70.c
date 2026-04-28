/*
Given vector of integers, return vector in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum && so on.

Examples:
strange_sort_vector({1, 2, 3, 4}) == {1, 4, 2, 3}
strange_sort_vector({5, 5, 5, 5}) == {5, 5, 5, 5}
strange_sort_vector({}) == {}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_70_pre_z: list Z -> Prop)
               (problem_70_spec_z: list Z -> list Z -> Prop)
               (copy_prefix: Z -> list Z -> list Z)
               (strange_output_prefix: Z -> Z -> list Z -> list Z)
               (strange_output: Z -> list Z -> list Z)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_70 */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= size && size < INT_MAX &&
        size == Zlength(l) &&
        IntArray::full(array, size, l)
    Ensure emp
*/;

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
        problem_70_spec_z(l, strange_output(init_size, sorted_l)) &&
        IntArray::full(array, size, sorted_full_l)
*/;

IntArray *strange_sort_list(int *lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_70_pre_z(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        exists data output_l,
        __return != 0 &&
        data != 0 &&
        lst_size == Zlength(output_l) &&
        problem_70_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), lst_size) *
        IntArray::full(lst, lst_size, input_l) *
        IntArray::full(data, lst_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = lst_size;
    out->data = malloc_int_array(lst_size);
    int *data = out->data;
    int *sorted = malloc_int_array(lst_size);
    int i;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        out != 0 &&
        data != 0 &&
        sorted != 0 &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_70_pre_z(input_l) &&
        0 <= i && i <= lst_size &&
        i == Zlength(copy_prefix(i, input_l)) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), lst_size) *
        IntArray::full(lst, lst_size, input_l) *
        IntArray::undef_full(data, lst_size) *
        IntArray::seg(sorted, 0, i, copy_prefix(i, input_l)) *
        IntArray::undef_seg(sorted, i, lst_size)
    */
    for (i = 0; i < lst_size; i++) {
        sorted[i] = lst[i];
    }

    /*@ Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        out != 0 &&
        data != 0 &&
        sorted != 0 &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_70_pre_z(input_l) &&
        copy_prefix(lst_size, input_l) == input_l &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), lst_size) *
        data_at(&i, lst_size) *
        IntArray::full(lst, lst_size, input_l) *
        IntArray::undef_full(data, lst_size) *
        IntArray::seg(sorted, 0, lst_size, input_l) *
        IntArray::undef_seg(sorted, lst_size, lst_size)
    */

    sort_int_array(sorted, lst_size, lst_size, 1);

    /*@ Inv Assert
        exists sorted_l sorted_full_l,
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        out != 0 &&
        data != 0 &&
        sorted != 0 &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        lst_size == Zlength(sorted_l) &&
        lst_size == Zlength(sorted_full_l) &&
        sublist(0, lst_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        problem_70_spec_z(input_l, strange_output(lst_size, sorted_l)) &&
        0 <= i && i <= lst_size &&
        (i < lst_size => 0 <= i / 2 && i / 2 < lst_size) &&
        (i < lst_size => 0 <= lst_size - 1 - i / 2 && lst_size - 1 - i / 2 < lst_size) &&
        i == Zlength(strange_output_prefix(lst_size, i, sorted_l)) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), lst_size) *
        IntArray::full(lst, lst_size, input_l) *
        IntArray::full(sorted, lst_size, sorted_full_l) *
        IntArray::seg(data, 0, i, strange_output_prefix(lst_size, i, sorted_l)) *
        IntArray::undef_seg(data, i, lst_size)
    */
    for (i = 0; i < lst_size; i++) {
        if (i % 2 == 0) {
            data[i] = sorted[i / 2];
        } else {
            data[i] = sorted[lst_size - 1 - (i / 2)];
        }
    }

    free_int_array(sorted, lst_size);
    return out;
}
