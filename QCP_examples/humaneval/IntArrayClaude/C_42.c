/*
Return vector with elements incremented by 1.
>>> incr_list({1, 2, 3})
{2, 3, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_42_pre: list Z -> Prop)
               (problem_42_spec: list Z -> list Z -> Prop)
               (list_incr_int_range: list Z -> Prop)
               (map_incr: list Z -> list Z) */
/*@ Import Coq Require Import coins_42 */

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

IntArray *incr_list(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        l_size == Zlength(input_l) &&
        problem_42_pre(input_l) &&
        list_incr_int_range(input_l) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == l_size &&
        output_size == Zlength(output_l) &&
        l_size == Zlength(input_l) &&
        output_l == map_incr(input_l) &&
        problem_42_spec(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(l, l_size, input_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    int i;
    IntArray *out = malloc_int_array_struct();
    out->size = l_size;
    out->data = malloc_int_array(l_size);
    int *data = out->data;
    /*@ Inv Assert
        l == l@pre &&
        l_size == l_size@pre &&
        out != 0 &&
        data != 0 &&
        l_size == Zlength(input_l) &&
        0 <= i && i <= l_size &&
        list_incr_int_range(input_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), l_size) *
        IntArray::full(l, l_size, input_l) *
        IntArray::seg(data, 0, i, map_incr(sublist(0, i, input_l))) *
        IntArray::undef_seg(data, i, l_size)
    */
    for (i = 0; i < l_size; ++i)
        data[i] = l[i] + 1;
    return out;
}
