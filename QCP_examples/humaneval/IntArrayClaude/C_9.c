/*
From a given vector of integers, generate a vector of rolling maximum element found until given moment
in the sequence. Output is written into pre-allocated array `out` of the same size.
>>> rolling_max({1, 2, 3, 2, 3, 4, 2}, out)
out = {1, 2, 3, 3, 3, 4, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (rolling_max_f: Z -> list Z -> list Z)
               (running_max_val: Z -> list Z -> Z) */

void rolling_max(int *numbers, int numbers_size, int *out)
/*@ With lv
    Require
        0 <= numbers_size && numbers_size < INT_MAX &&
        IntArray::full(numbers, numbers_size, lv) *
        IntArray::undef_full(out, numbers_size)
    Ensure
        IntArray::full(numbers, numbers_size, lv) *
        IntArray::full(out, numbers_size, rolling_max_f(0, lv))
*/
{
    int i;
    int max = 0;
    /*@ Inv
        0 <= i && i <= numbers_size@pre &&
        max == running_max_val(0, sublist(0, i, lv)) &&
        IntArray::full(numbers, numbers_size@pre, lv) *
        IntArray::seg(out@pre, 0, i, rolling_max_f(0, sublist(0, i, lv))) *
        IntArray::undef_seg(out@pre, i, numbers_size@pre)
    */
    for (i = 0; i < numbers_size; ++i) {
        if (numbers[i] > max) max = numbers[i];
        out[i] = max;
    }
}
