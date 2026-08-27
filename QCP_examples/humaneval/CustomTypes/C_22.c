/*
Filter given vector of any python values only for integers
>>> filter_integers({"a", 3.14, 5})
{5}
>>> filter_integers({1, 2, 3, "abc", {}, {}})
{1, 2, 3}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (py_value :: *) */
/*@ Extern Coq (problem_22_pre_z : list py_value -> Prop)
               (problem_22_spec_z : list py_value -> list Z -> Prop)
               (py_value_tags : list py_value -> list Z)
               (py_value_payloads : list py_value -> list Z)
               (filter_tagged : list Z -> list Z -> list Z) */
/*@ Import Coq Require Import coins_22 */

typedef enum {
    PY_INT,
    PY_DOUBLE,
    PY_STRING
} PyType;

/*
 * QCP interface adaptation: the original PyValue array is represented by two
 * parallel arrays.  types[i] is the PyType tag and int_values[i] is the integer
 * payload.  Non-integer payloads are ignored, exactly as in the original loop.
 */
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
/*@ Require 0 <= size && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *filter_integers(int *types, int *int_values, int values_size)
/*@ With (input_l : list py_value) (types_l ints_l : list Z)
    Require
        0 <= values_size && values_size < INT_MAX &&
        types_l == py_value_tags(input_l) &&
        ints_l == py_value_payloads(input_l) &&
        values_size == Zlength(types_l) &&
        values_size == Zlength(ints_l) &&
        problem_22_pre_z(input_l) &&
        IntArray::full(types, values_size, types_l) *
        IntArray::full(int_values, values_size, ints_l)
    Ensure
        exists data output_l output_size,
        __return != 0 && data != 0 &&
        0 <= output_size && output_size <= values_size &&
        output_size == Zlength(output_l) &&
        problem_22_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(types, values_size, types_l) *
        IntArray::full(int_values, values_size, ints_l) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, values_size)
*/
{
    int i;
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(values_size);
    int *data = out->data;

    /*@ Inv Assert
        exists output_l output_size,
        types == types@pre &&
        int_values == int_values@pre &&
        values_size == values_size@pre &&
        types_l == py_value_tags(input_l) &&
        ints_l == py_value_payloads(input_l) &&
        values_size == Zlength(types_l) &&
        values_size == Zlength(ints_l) &&
        0 <= i && i <= values_size &&
        0 <= output_size && output_size <= i &&
        output_size == Zlength(output_l) &&
        output_l == filter_tagged(sublist(0, i, types_l),
                                  sublist(0, i, ints_l)) &&
        out != 0 && data != 0 &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), output_size) *
        IntArray::full(types, values_size, types_l) *
        IntArray::full(int_values, values_size, ints_l) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, values_size)
    */
    for (i = 0; i < values_size; i = i + 1) {
        if (types[i] == PY_INT) {
            data[out->size] = int_values[i];
            out->size = out->size + 1;
        }
    }
    return out;
}
