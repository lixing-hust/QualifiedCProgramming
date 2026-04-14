/*
Insert a number "delimeter" between every two consecutive elements of input vector `numbers`.
The output buffer is provided by the caller, and the function returns `out`.
>>> intersperse({}, 4, out)
out = {}
>>> intersperse({1, 2, 3}, 4, out)
out = {1, 4, 2, 4, 3}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_5_pre: list Z -> list Z -> Prop) */
/*@ Extern Coq (problem_5_spec: list Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (int_value_range: Z -> Prop) */
/*@ Extern Coq (intersperse_list: list Z -> Z -> list Z) */
/*@ Import Coq Require Import coins_5 */

int *intersperse(const int *numbers, int numbers_size, int delimeter, int *out, int out_size)
/*@ With input_l (numbers0: Z) (numbers_size0: Z) (delimeter0: Z) (out0: Z) (out_size0: Z)
    Require
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        delimeter == delimeter0 &&
        out == out0 &&
        out_size == out_size0 &&
        0 <= numbers_size0 && numbers_size0 < INT_MAX &&
        ((numbers_size0 == 0 && out_size0 == 0) ||
         (0 < numbers_size0 && out_size0 == 2 * numbers_size0 - 1)) &&
        0 <= out_size0 && out_size0 < INT_MAX &&
        int_value_range(delimeter0) &&
        IntArray::full(numbers, numbers_size, input_l) *
        IntArray::undef_full(out, out_size)
    Ensure
        exists output_l,
        __return == out0 &&
        problem_5_pre(input_l, output_l) &&
        problem_5_spec(input_l, output_l, delimeter0) &&
        IntArray::full(numbers0, numbers_size0, input_l) *
        IntArray::full(out0, out_size0, output_l)
*/
{
    int k = 0;
    if (numbers_size == 0) {
        return out;
    }

    out[k] = numbers[0];
    k = k + 1;

    int i;
    /*@ Inv Assert
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        delimeter == delimeter0 &&
        out == out0 &&
        out_size == out_size0 &&
        1 <= i && i <= numbers_size &&
        out_size == 2 * numbers_size - 1 &&
        0 < out_size && out_size < INT_MAX &&
        k == 2 * i - 1 &&
        IntArray::full(numbers, numbers_size, input_l) *
        IntArray::seg(out, 0, k, intersperse_list(sublist(0, i, input_l), delimeter)) *
        IntArray::undef_seg(out, k, out_size)
    */
    for (i = 1; i < numbers_size; i++) {
        out[k] = delimeter;
        k = k + 1;
        out[k] = numbers[i];
        k = k + 1;
    }

    return out;
}
