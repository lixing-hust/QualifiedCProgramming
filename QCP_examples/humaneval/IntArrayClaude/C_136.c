/*
Create a function that returns a vector (a, b), where "a" is
the largest of negative integers, && "b" is the smallest
of positive integers in a vector.
If there is no negative || positive integers, return them as 0.

Examples:
largest_smallest_integers({2, 4, 1, 3, 5, 7}) == {0, 1}
largest_smallest_integers({}) == {0,0}
largest_smallest_integers({0}) == {0,0}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_136_pre_z: list Z -> Prop)
               (problem_136_spec_z: list Z -> list Z -> Prop)
               (largest_smallest_prefix: Z -> list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_136 */

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

IntArray *largest_smallest_integers(int* lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_136_pre_z(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == 2 &&
        output_size == Zlength(output_l) &&
        problem_136_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(lst, lst_size, input_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    int maxneg = 0, minpos = 0;
    int i;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_136_pre_z(input_l) &&
        0 <= i && i <= lst_size &&
        largest_smallest_prefix(i, input_l, maxneg, minpos) &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i = 0; i < lst_size; i++)
    {
        if (lst[i] < 0 && (maxneg == 0 || lst[i] > maxneg)) maxneg = lst[i];
        if (lst[i] > 0 && (minpos == 0 || lst[i] < minpos)) minpos = lst[i];
    }
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = maxneg;
    data[1] = minpos;
    return out;
}
