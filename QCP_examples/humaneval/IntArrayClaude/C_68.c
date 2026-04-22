/*
Given a vector representing a branch of a tree that has non-negative integer nodes
your task is to pluck one of the nodes && return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a vector, { smalest_value, its index },
If there are no even values || the given vector is empty, return {}.

Example 1:
    Input: {4,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 2:
    Input: {1,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index. 

Example 3:
    Input: {}
    Output: {}

Example 4:
    Input: {5, 0, 3, 0, 4, 2}
    Output: {0, 1}
    Explanation: 0 is the smallest value, but  there are two zeros,
                 so we will choose the first zero, which has the smallest index.

Constraints:
    * 1 <= nodes.length <= 10000
    * 0 <= node.value
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_68_pre_z: list Z -> Prop)
               (problem_68_spec_z: list Z -> list Z -> Prop)
               (list_nonnegative: list Z -> Prop)
               (pluck_loop_state: list Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_68 */

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

IntArray *pluck(int *arr, int arr_size)
/*@ With input_l
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_68_pre_z(input_l) &&
        list_nonnegative(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        0 <= output_size && output_size <= 2 &&
        (output_size == 0 || output_size == 2) &&
        output_size == Zlength(output_l) &&
        problem_68_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(arr, arr_size, input_l) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, 2)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 0;
    int *data = out->data;
    int i;

    /*@ Inv Assert
        exists output_l output_size,
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        0 <= i && i <= arr_size &&
        0 <= output_size && output_size <= 2 &&
        (output_size == 0 || output_size == 2) &&
        output_size == Zlength(output_l) &&
        list_nonnegative(input_l) &&
        pluck_loop_state(input_l, i, output_l) &&
        data_at(&(out -> data), data) *
        IntArray::full(arr, arr_size, input_l) *
        ((output_size == 0 &&
          output_l == nil &&
          data_at(&(out -> size), 0) *
          IntArray::undef_full(data, 2)) ||
         (exists value index,
          output_size == 2 &&
          output_l == cons(value, cons(index, nil)) &&
          data_at(&(out -> size), 2) *
          IntArray::full(data, 2, output_l)))
    */
    for (i = 0; i < arr_size; i++) {
        if (arr[i] % 2 == 0 && (out->size == 0 || arr[i] < data[0])) {
            data[0] = arr[i];
            data[1] = i;
            out->size = 2;
        }
    }

    return out;
}
