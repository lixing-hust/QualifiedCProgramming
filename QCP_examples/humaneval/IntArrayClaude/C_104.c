/*
Given a vector of positive integers x. return a sorted vector of all
elements that hasn't any even digit.

Note: Returned vector should be sorted in increasing order.

For example:
>>> unique_digits({15, 33, 1422, 1})
{1, 15, 33}
>>> unique_digits({152, 323, 1422, 10})
{}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_104_pre_z: list Z -> Prop)
               (problem_104_spec_z: list Z -> list Z -> Prop)
               (unique_digits_prefix: list Z -> Z -> list Z -> Prop)
               (odd_digit_scan_state: Z -> Z -> Z -> Prop)
               (only_odd_digits_z: Z -> Prop)
               (has_even_digit_z: Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_104 */

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
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        sublist(0, init_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, sorted_full_l)
*/;

int has_only_odd_digits_int(int value)
/*@ Require
        0 < value && value < INT_MAX
    Ensure
        ((__return != 0) && only_odd_digits_z(value) ||
         (__return == 0) && has_even_digit_z(value))
*/
{
    int num = value;
    int u = 1;
    if (num == 0) {
        u = 0;
    }

    /*@ Inv Assert
        value == value@pre &&
        0 < value && value < INT_MAX &&
        0 <= num && num <= value &&
        (u == 0 || u == 1) &&
        odd_digit_scan_state(value, num, u)
    */
    while (num > 0 && u) {
        if (num % 2 == 0) {
            u = 0;
        }
        num = num / 10;
    }
    return u;
}

IntArray *unique_digits(int *x, int x_size)
/*@ With input_l
    Require
        0 <= x_size && x_size < INT_MAX &&
        x_size == Zlength(input_l) &&
        problem_104_pre_z(input_l) &&
        IntArray::full(x, x_size, input_l)
    Ensure
        exists data output_l output_size data_l,
        __return != 0 &&
        data != 0 &&
        0 <= output_size && output_size <= x_size &&
        output_size == Zlength(output_l) &&
        x_size == Zlength(data_l) &&
        sublist(0, output_size, data_l) == output_l &&
        problem_104_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, x_size, data_l) *
        IntArray::full(x, x_size, input_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(x_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    /*@ Inv Assert
        exists output_l,
        x == x@pre &&
        x_size == x_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= x_size && x_size < INT_MAX &&
        x_size == Zlength(input_l) &&
        problem_104_pre_z(input_l) &&
        0 <= i && i <= x_size &&
        0 <= output_size && output_size <= i &&
        output_size == Zlength(output_l) &&
        unique_digits_prefix(input_l, i, output_l) &&
        IntArray::full(x, x_size, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, x_size)
    */
    for (i = 0; i < x_size; i++) {
        int current = x[i];
        int u = has_only_odd_digits_int(current);
        if (u) {
            data[output_size] = current;
            output_size = output_size + 1;
        }
    }

    /*@ Assert
        exists output_l,
        x == x@pre &&
        x_size == x_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= x_size && x_size < INT_MAX &&
        x_size == Zlength(input_l) &&
        problem_104_pre_z(input_l) &&
        0 <= output_size && output_size <= x_size &&
        output_size == Zlength(output_l) &&
        unique_digits_prefix(input_l, x_size, output_l) &&
        IntArray::full(x, x_size, input_l) *
        data_at(&i, x_size) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, x_size)
    */
    sort_int_array(data, output_size, x_size, 1);

    /*@ Assert
        exists output_l sorted_l data_l,
        x == x@pre &&
        x_size == x_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= x_size && x_size < INT_MAX &&
        x_size == Zlength(input_l) &&
        problem_104_pre_z(input_l) &&
        0 <= output_size && output_size <= x_size &&
        output_size == Zlength(output_l) &&
        output_size == Zlength(sorted_l) &&
        x_size == Zlength(data_l) &&
        sublist(0, output_size, data_l) == sorted_l &&
        unique_digits_prefix(input_l, x_size, output_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(output_l, sorted_l) &&
        problem_104_spec_z(input_l, sorted_l) &&
        IntArray::full(x, x_size, input_l) *
        data_at(&i, x_size) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(data, x_size, data_l)
    */
    out->size = output_size;
    return out;
}
