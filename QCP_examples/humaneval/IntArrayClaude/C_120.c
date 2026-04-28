/*
Given a vector arr of integers && a positive integer k, return a sorted vector
of length k with the maximum k numbers in arr.

Example 1:

    Input: arr = {-3, -4, 5}, k = 3
    Output: {-4, -3, 5}

Example 2:

    Input: arr = {4, -4, 4}, k = 2
    Output: {4, 4}

Example 3:

    Input: arr = {-3, 2, 1, 2, -1, -2, 1}, k = 1
    Output: {2}

Note:
    1. The length of the vector will be in the range of {1, 1000}.
    2. The elements in the vector will be in the range of {-1000, 1000}.
    3. 0 <= k <= len(arr)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_120_pre_z: list Z -> Z -> Prop)
               (problem_120_spec_z: list Z -> Z -> list Z -> Prop)
               (copy_prefix: list Z -> Z -> list Z)
               (maximum_output_prefix: list Z -> Z -> Z -> Z -> list Z)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_120 */

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
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        sublist(0, init_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, sorted_full_l)
*/;

IntArray *maximum(int *arr, int arr_size, int k)
/*@ With input_l
    Require
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 <= k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        problem_120_pre_z(input_l, k) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        exists data output_l,
        __return != 0 &&
        data != 0 &&
        k == Zlength(output_l) &&
        problem_120_spec_z(input_l, k, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), k) *
        IntArray::full(data, k, output_l) *
        IntArray::full(arr, arr_size, input_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->data = 0;
    out->size = 0;

    if (k <= 0) {
        out->data = malloc_int_array(0);
        out->size = 0;
        return out;
    }

    int *tmp = malloc_int_array(arr_size);
    int i;

    /*@ Inv Assert
        exists tmp_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        out != 0 &&
        tmp != 0 &&
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 < k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        problem_120_pre_z(input_l, k) &&
        0 <= i && i <= arr_size &&
        i == Zlength(tmp_l) &&
        tmp_l == copy_prefix(input_l, i) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&(out -> data), 0) *
        data_at(&(out -> size), 0) *
        IntArray::seg(tmp, 0, i, tmp_l) *
        IntArray::undef_seg(tmp, i, arr_size)
    */
    for (i = 0; i < arr_size; i++) {
        tmp[i] = arr[i];
    }

    /*@ Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        out != 0 &&
        tmp != 0 &&
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 < k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        problem_120_pre_z(input_l, k) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&i, arr_size) *
        data_at(&(out -> data), 0) *
        data_at(&(out -> size), 0) *
        IntArray::seg(tmp, 0, arr_size, input_l) *
        IntArray::undef_seg(tmp, arr_size, arr_size)
    */
    sort_int_array(tmp, arr_size, arr_size, 1);

    /*@ Assert
        exists sorted_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        out != 0 &&
        tmp != 0 &&
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 < k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_120_pre_z(input_l, k) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&i, arr_size) *
        data_at(&(out -> data), 0) *
        data_at(&(out -> size), 0) *
        IntArray::full(tmp, arr_size, sorted_l)
    */

    out->data = malloc_int_array(k);
    int *data = out->data;

    /*@ Inv Assert
        exists sorted_l output_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        out != 0 &&
        tmp != 0 &&
        data != 0 &&
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 < k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_120_pre_z(input_l, k) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        0 <= i && i <= k &&
        i == Zlength(output_l) &&
        output_l == maximum_output_prefix(sorted_l, arr_size, k, i) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(tmp, arr_size, sorted_l) *
        IntArray::seg(data, 0, i, output_l) *
        IntArray::undef_seg(data, i, k)
    */
    for (i = 0; i < k; i++) {
        data[i] = tmp[arr_size - k + i];
    }

    /*@ Assert
        exists sorted_l output_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        k == k@pre &&
        out != 0 &&
        tmp != 0 &&
        data != 0 &&
        arr != 0 &&
        1 <= arr_size && arr_size <= 1000 &&
        0 < k && k <= arr_size &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_120_pre_z(input_l, k) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        k == Zlength(output_l) &&
        problem_120_spec_z(input_l, k, output_l) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&i, k) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(tmp, arr_size, sorted_l) *
        IntArray::full(data, k, output_l)
    */
    out->size = k;
    free_int_array(tmp, arr_size);
    return out;
}
