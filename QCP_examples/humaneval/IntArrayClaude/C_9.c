/*
From a given vector of integers, generate a vector of rolling maximum element found until given moment
in the sequence. Output is written into pre-allocated array `out` of the same size.
>>> rolling_max({1, 2, 3, 2, 3, 4, 2}, out)
out = {1, 2, 3, 3, 3, 4, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_9_pre: Prop)
               (problem_9_spec: list Z -> list Z -> Prop)
               (list_int_range: list Z -> Prop)
               (rolling_max_f: Z -> list Z -> list Z)
               (running_max_val: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_9 */

int *rolling_max(int *numbers, int numbers_size, int *out, int out_size)
/*@ With lv (numbers0: Z) (numbers_size0: Z) (out0: Z) (out_size0: Z)
    Require
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        out == out0 &&
        out_size == out_size0 &&
        0 <= numbers_size0 && numbers_size0 < INT_MAX &&
        out_size0 == numbers_size0 &&
        problem_9_pre &&
        list_int_range(lv) &&
        IntArray::full(numbers, numbers_size, lv) *
        IntArray::undef_full(out, out_size)
    Ensure
        exists output_l,
        __return == out0 &&
        problem_9_pre &&
        problem_9_spec(lv, output_l) &&
        IntArray::full(numbers0, numbers_size0, lv) *
        IntArray::full(out0, out_size0, output_l)
*/
{
    int i;
    int max = -2147483648;
    /*@ Inv Assert
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        out == out0 &&
        out_size == out_size0 &&
        out_size == numbers_size &&
        list_int_range(lv) &&
        0 <= i && i <= numbers_size &&
        max == running_max_val(INT_MIN, sublist(0, i, lv)) &&
        IntArray::full(numbers, numbers_size, lv) *
        IntArray::seg(out, 0, i, rolling_max_f(INT_MIN, sublist(0, i, lv))) *
        IntArray::undef_seg(out, i, out_size)
    */
    for (i = 0; i < numbers_size; ++i) {
        if (numbers[i] > max) max = numbers[i];
        out[i] = max;
    }

    return out;
}
