/*
Return sorted unique common elements for two vectors.
>>> common({1, 4, 3, 34, 653, 2, 5}, {5, 7, 1, 5, 9, 653, 121})
{1, 5, 653}
>>> common({5, 3, 2, 8}, {3, 2})
{2, 3}

*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_58_pre_z: list Z -> list Z -> Prop)
               (problem_58_spec_z: list Z -> list Z -> list Z -> Prop)
               (list_contains: Z -> list Z -> Prop)
               (list_not_contains: Z -> list Z -> Prop)
               (common_first_loop: list Z -> list Z -> Z -> list Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_58 */

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

int contains(int *a, int n, int x)
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        n == Zlength(l) &&
        IntArray::seg(a, 0, n, l)
    Ensure
        ((__return != 0) && list_contains(x, l) ||
         (__return == 0) && list_not_contains(x, l)) &&
        n == Zlength(l) &&
        IntArray::seg(a, 0, n, l)
*/
{
    int i;
    /*@ Inv Assert
        a == a@pre && n == n@pre && x == x@pre &&
        n == Zlength(l) &&
        0 <= i && i <= n &&
        (forall (k: Z), 0 <= k && k < i => Znth(k, l, 0) != x) &&
        IntArray::seg(a, 0, n, l)
    */
    for (i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }
    return 0;
}

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

IntArray *common(int *l1, int l1_size, int *l2, int l2_size)
/*@ With input_l1 input_l2
    Require
        0 <= l1_size && l1_size < INT_MAX &&
        0 <= l2_size && l2_size < INT_MAX &&
        l1_size == Zlength(input_l1) &&
        l2_size == Zlength(input_l2) &&
        problem_58_pre_z(input_l1, input_l2) &&
        IntArray::full(l1, l1_size, input_l1) *
        IntArray::full(l2, l2_size, input_l2)
    Ensure
        exists data output_l output_size data_l,
        __return != 0 &&
        data != 0 &&
        0 <= output_size && output_size <= l1_size &&
        output_size == Zlength(output_l) &&
        l1_size == Zlength(data_l) &&
        sublist(0, output_size, data_l) == output_l &&
        problem_58_spec_z(input_l1, input_l2, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(l1, l1_size, input_l1) *
        IntArray::full(l2, l2_size, input_l2) *
        IntArray::full(data, l1_size, data_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(l1_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    /*@ Inv Assert
        exists output_l,
        l1 == l1@pre &&
        l1_size == l1_size@pre &&
        l2 == l2@pre &&
        l2_size == l2_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= l1_size && l1_size < INT_MAX &&
        0 <= l2_size && l2_size < INT_MAX &&
        l1_size == Zlength(input_l1) &&
        l2_size == Zlength(input_l2) &&
        problem_58_pre_z(input_l1, input_l2) &&
        0 <= i && i <= l1_size &&
        0 <= output_size && output_size <= i &&
        output_size == Zlength(output_l) &&
        common_first_loop(input_l1, input_l2, i, output_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(l1, l1_size, input_l1) *
        IntArray::seg(l2, 0, l2_size, input_l2) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, l1_size)
    */
    for (i = 0; i < l1_size; i++) {
        int current = l1[i];
        int in_output = contains(data, output_size, current);
        if (!in_output) {
            int in_l2 = contains(l2, l2_size, current);
            if (in_l2) {
                data[output_size] = current;
                output_size = output_size + 1;
            }
        }
    }

    sort_int_array(data, output_size, l1_size, 1);
    out->size = output_size;
    return out;
}
