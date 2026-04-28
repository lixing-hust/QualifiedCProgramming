/*
Given a vector of non-negative integers, return a copy of the given vector after sorting,
you will sort the given vector in ascending order if the sum( first index value, last index value) is odd,
|| sort it in descending order if the sum( first index value, last index value) is even.

Note:
* don't change the given vector.

Examples:
* sort_vector({}) => {}
* sort_vector({5}) => {5}
* sort_vector({2, 4, 3, 0, 1, 5}) => {0, 1, 2, 3, 4, 5}
* sort_vector({2, 4, 3, 0, 1, 5, 6}) => {6, 5, 4, 3, 2, 1, 0}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_88_pre_z: list Z -> Prop)
               (problem_88_spec_z: list Z -> list Z -> Prop)
               (sort_array_input_range: list Z -> Prop)
               (copy_prefix: Z -> list Z -> list Z)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (reverse_loop: Z -> Z -> list Z -> list Z)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_88 */

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

void sort_int_array(int *array, int size)
/*@ With l input_l
    Require
        array != 0 &&
        size == Zlength(l) &&
        size == Zlength(input_l) &&
        0 <= size && size < INT_MAX &&
        sort_array_input_range(input_l) &&
        IntArray::full(array, size, l)
    Ensure
        exists sorted_l,
        size == Zlength(sorted_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(l, sorted_l) &&
        ((size == 0 || (Znth(0, input_l, 0) + Znth(size - 1, input_l, 0)) % 2 != 0) =>
            problem_88_spec_z(input_l, sorted_l)) &&
        (0 < size && (Znth(0, input_l, 0) + Znth(size - 1, input_l, 0)) % 2 == 0 =>
            problem_88_spec_z(input_l, reverse_loop(size, size / 2, sorted_l))) &&
        IntArray::full(array, size, sorted_l)
*/;

IntArray *sort_array(int *array, int array_size)
/*@ With input_l
    Require
        0 <= array_size && array_size < INT_MAX &&
        array_size == Zlength(input_l) &&
        problem_88_pre_z(input_l) &&
        sort_array_input_range(input_l) &&
        IntArray::full(array, array_size, input_l)
    Ensure
        exists data output_l,
        __return != 0 &&
        data != 0 &&
        array_size == Zlength(output_l) &&
        problem_88_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), array_size) *
        IntArray::full(array, array_size, input_l) *
        IntArray::full(data, array_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = array_size;
    out->data = malloc_int_array(array_size);
    int *data = out->data;
    int i;
    int t = 0;

    if (array_size == 0) {
        return out;
    }

    /*@ Inv Assert
        exists t_v,
        array == array@pre &&
        array_size == array_size@pre &&
        out != 0 &&
        data != 0 &&
        0 < array_size && array_size < INT_MAX &&
        array_size == Zlength(input_l) &&
        problem_88_pre_z(input_l) &&
        sort_array_input_range(input_l) &&
        0 <= i && i <= array_size &&
        i == Zlength(copy_prefix(i, input_l)) &&
        IntArray::full(array, array_size, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), array_size) *
        data_at(&t, t_v) *
        IntArray::seg(data, 0, i, copy_prefix(i, input_l)) *
        IntArray::undef_seg(data, i, array_size)
    */
    for (i = 0; i < array_size; i++) {
        data[i] = array[i];
    }

    /*@ Assert
        exists t_v,
        array == array@pre &&
        array_size == array_size@pre &&
        out != 0 &&
        data != 0 &&
        0 < array_size && array_size < INT_MAX &&
        array_size == Zlength(input_l) &&
        problem_88_pre_z(input_l) &&
        sort_array_input_range(input_l) &&
        copy_prefix(array_size, input_l) == input_l &&
        IntArray::full(array, array_size, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), array_size) *
        data_at(&i, array_size) *
        data_at(&t, t_v) *
        IntArray::full(data, array_size, input_l)
    */

    sort_int_array(data, array_size);

    if ((array[0] + array[array_size - 1]) % 2 == 0)
    {
        /*@ Inv Assert
            exists sorted_l t_v,
            array == array@pre &&
            array_size == array_size@pre &&
            out != 0 &&
            data != 0 &&
            0 < array_size && array_size < INT_MAX &&
            array_size == Zlength(input_l) &&
            array_size == Zlength(sorted_l) &&
            problem_88_pre_z(input_l) &&
            sort_array_input_range(input_l) &&
            sorted_int_list_by(1, sorted_l) &&
            Permutation(input_l, sorted_l) &&
            problem_88_spec_z(input_l, reverse_loop(array_size, array_size / 2, sorted_l)) &&
            (Znth(0, input_l, 0) + Znth(array_size - 1, input_l, 0)) % 2 == 0 &&
            0 <= i && i <= array_size / 2 &&
            (i < array_size / 2 => 0 <= i && i < array_size) &&
            (i < array_size / 2 => 0 <= array_size - 1 - i && array_size - 1 - i < array_size) &&
            array_size == Zlength(reverse_loop(array_size, i, sorted_l)) &&
            IntArray::full(array, array_size, input_l) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), array_size) *
            data_at(&t, t_v) *
            IntArray::full(data, array_size, reverse_loop(array_size, i, sorted_l))
        */
        for (i = 0; i < array_size / 2; i++) {
            t = data[i];
            data[i] = data[array_size - 1 - i];
            data[array_size - 1 - i] = t;
        }
    }
    return out;
}
