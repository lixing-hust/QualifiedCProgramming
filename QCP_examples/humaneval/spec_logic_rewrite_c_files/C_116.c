/*
In this Kata, you have to sort a vector of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_vector({1, 5, 2, 3, 4}) == {1, 2, 3, 4, 5}
>>> sort_vector({-2, -3, -4, -5, -6}) == {-6, -5, -4, -3, -2}
>>> sort_vector({1, 0, 2, 3, 4}) == {0, 1, 2, 3, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_116_pre_z: list Z -> Prop)
               (problem_116_spec_z: list Z -> list Z -> Prop)
               (sort_array_116_int_range: list Z -> Prop)
               (bit_count_state_116: Z -> Z -> Z -> Prop)
               (bit_count_state_at_116: Z -> list Z -> Z -> Z -> Prop)
               (bit_count_result_116: Z -> Z -> Prop)
               (sort_copy_prefix_116: Z -> list Z -> list Z -> Prop)
               (sort_score_prefix_116: Z -> list Z -> list Z -> Prop)
               (sort_outer_state_116: Z -> list Z -> list Z -> list Z -> Prop)
               (sort_inner_state_116: Z -> Z -> list Z -> list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_116 */

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
/*@ With l
    Require
        array != 0 &&
        0 <= size && size < INT_MAX &&
        size == Zlength(l) &&
        IntArray::full(array, size, l)
    Ensure emp
*/;

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

IntArray *sort_array(int* arr, int arr_size)
/*@ With input_l
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_116_pre_z(input_l) &&
        sort_array_116_int_range(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == arr_size &&
        output_size == Zlength(output_l) &&
        problem_116_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    int* bin = 0;
    int m = 0;

    out->size = arr_size;
    out->data = malloc_int_array(arr_size);
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    int i;
    /*@ Inv Assert
        exists output_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        bin == bin &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_116_pre_z(input_l) &&
        sort_array_116_int_range(input_l) &&
        0 <= i && i <= arr_size &&
        i == Zlength(output_l) &&
        sort_copy_prefix_116(i, input_l, output_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), arr_size) *
        data_at(&m, m) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::seg(data, 0, i, output_l) *
        IntArray::undef_seg(data, i, arr_size)
    */
    for (i = 0; i < arr_size; i++) {
        data[i] = arr[i];
        /*@ Assert
            exists output_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin == bin &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            i + 1 == Zlength(output_l) &&
            sort_copy_prefix_116(i + 1, input_l, output_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::seg(data, 0, i + 1, output_l) *
            IntArray::undef_seg(data, i + 1, arr_size)
        */
    }
    /*@ Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        bin == bin &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_116_pre_z(input_l) &&
        sort_array_116_int_range(input_l) &&
        data_at(&i, arr_size) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), arr_size) *
        data_at(&m, m) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::full(data, arr_size, input_l)
    */

    bin = malloc_int_array(arr_size);
    if (bin == 0) {
        free_int_array(data, arr_size);
        out->data = 0;
        out->size = 0;
        return out;
    }
    /*@ Inv Assert
        exists score_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        bin != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_116_pre_z(input_l) &&
        sort_array_116_int_range(input_l) &&
        0 <= i && i <= arr_size &&
        i == Zlength(score_l) &&
        sort_score_prefix_116(i, input_l, score_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), arr_size) *
        data_at(&m, m) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::full(data, arr_size, input_l) *
        IntArray::seg(bin, 0, i, score_l) *
        IntArray::undef_seg(bin, i, arr_size)
    */
    for (i=0;i<arr_size;i++)
    {
        int b = 0;
        int n = 0;
        /*@ Assert
            exists score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            b == b &&
            n == n &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            i == Zlength(score_l) &&
            sort_score_prefix_116(i, input_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, input_l) *
            IntArray::seg(bin, 0, i, score_l) *
            IntArray::undef_seg(bin, i, arr_size)
        */
        n = out->data[i];
        n = abs(n);
        b = 0;
        /*@ Assert
            exists score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            b == 0 &&
            n == Zabs(Znth(i, input_l, 0)) &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            i == Zlength(score_l) &&
            sort_score_prefix_116(i, input_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, input_l) *
            IntArray::seg(bin, 0, i, score_l) *
            IntArray::undef_seg(bin, i, arr_size)
        */
        /*@ Inv Assert
            exists score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            b == b &&
            n == n &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            i == Zlength(score_l) &&
            sort_score_prefix_116(i, input_l, score_l) &&
            0 <= n && n < INT_MAX &&
            0 <= b && b <= 31 &&
            bit_count_state_at_116(i, input_l, n, b) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, input_l) *
            IntArray::seg(bin, 0, i, score_l) *
            IntArray::undef_seg(bin, i, arr_size)
        */
        while (n>0)
        {
            b+=n%2;n=n/2;
        }
        bin[i] = b;
        /*@ Assert
            exists score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            b == b &&
            n == n &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            i + 1 == Zlength(score_l) &&
            sort_score_prefix_116(i + 1, input_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, input_l) *
            IntArray::seg(bin, 0, i + 1, score_l) *
            IntArray::undef_seg(bin, i + 1, arr_size)
        */
    }
    /*@ Inv Assert
        exists output_l score_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        bin != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_116_pre_z(input_l) &&
        sort_array_116_int_range(input_l) &&
        0 <= i && i <= arr_size &&
        arr_size == Zlength(output_l) &&
        arr_size == Zlength(score_l) &&
        sort_outer_state_116(i, input_l, output_l, score_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), arr_size) *
        data_at(&m, m) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::full(data, arr_size, output_l) *
        IntArray::full(bin, arr_size, score_l)
    */
    for (i=0;i<arr_size;i++)
    {
        int j;
        /*@ Inv Assert
            exists output_l score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            1 <= j && j <= arr_size &&
            arr_size == Zlength(output_l) &&
            arr_size == Zlength(score_l) &&
            sort_inner_state_116(i, j, input_l, output_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, output_l) *
            IntArray::full(bin, arr_size, score_l)
        */
        for (j=1;j<arr_size;j++)
        if (bin[j]<bin[j-1] || (bin[j]==bin[j-1] && data[j]<data[j-1]))
        {
            m=out->data[j];out->data[j]=out->data[j-1];out->data[j-1]=m;
            m=bin[j];bin[j]=bin[j-1];bin[j-1]=m;
        }
        /*@ Assert
            exists output_l score_l,
            arr == arr@pre &&
            arr_size == arr_size@pre &&
            out != 0 &&
            data != 0 &&
            bin != 0 &&
            0 <= arr_size && arr_size < INT_MAX &&
            arr_size == Zlength(input_l) &&
            problem_116_pre_z(input_l) &&
            sort_array_116_int_range(input_l) &&
            0 <= i && i < arr_size &&
            arr_size == Zlength(output_l) &&
            arr_size == Zlength(score_l) &&
            sort_outer_state_116(i + 1, input_l, output_l, score_l) &&
            data_at(&j, arr_size) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), arr_size) *
            data_at(&m, m) *
            IntArray::full(arr, arr_size, input_l) *
            IntArray::full(data, arr_size, output_l) *
            IntArray::full(bin, arr_size, score_l)
        */
    }
    /*@ Assert
        exists output_l score_l,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        bin != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(output_l) &&
        arr_size == Zlength(score_l) &&
        problem_116_spec_z(input_l, output_l) &&
        data_at(&i, arr_size) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), arr_size) *
        data_at(&m, m) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::full(data, arr_size, output_l) *
        IntArray::full(bin, arr_size, score_l)
    */
    free_int_array(bin, arr_size);
    return out;
}
