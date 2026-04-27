/*
Return sorted unique elements in a vector
>>> unique({5, 3, 5, 2, 3, 3, 9, 0, 123})
{0, 2, 3, 5, 9, 123}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_34_pre_z: list Z -> Prop)
               (problem_34_spec_z: list Z -> list Z -> Prop)
               (list_contains: Z -> list Z -> Prop)
               (list_not_contains: Z -> list Z -> Prop)
               (unique_first_loop: list Z -> Z -> list Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_34 */

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

IntArray *unique(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        l_size == Zlength(input_l) &&
        problem_34_pre_z(input_l) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        exists data output_l output_size data_l,
        __return != 0 &&
        data != 0 &&
        0 <= output_size && output_size <= l_size &&
        output_size == Zlength(output_l) &&
        l_size == Zlength(data_l) &&
        sublist(0, output_size, data_l) == output_l &&
        problem_34_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(l, l_size, input_l) *
        IntArray::full(data, l_size, data_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(l_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    /*@ Inv Assert
        exists output_l,
        l == l@pre &&
        l_size == l_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= l_size && l_size < INT_MAX &&
        l_size == Zlength(input_l) &&
        problem_34_pre_z(input_l) &&
        0 <= i && i <= l_size &&
        0 <= output_size && output_size <= i &&
        output_size == Zlength(output_l) &&
        unique_first_loop(input_l, i, output_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(l, l_size, input_l) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, l_size)
    */
    for (i = 0; i < l_size; i++) {
        int current = l[i];
        int in_output = contains(data, output_size, current);
        if (!in_output) {
            data[output_size] = current;
            output_size = output_size + 1;
        }
    }
    sort_int_array(data, output_size, l_size, 1);
    out->size = output_size;
    return out;
}
