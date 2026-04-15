/*
For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> sum_product({})
(0, 1)
>>> sum_product({1, 2, 3, 4})
(10, 24)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_8_pre: Prop)
               (problem_8_spec: list Z -> Z -> Z -> Prop)
               (list_int_range: list Z -> Prop)
               (prefix_sum: list Z -> Z -> Z)
               (prefix_product: list Z -> Z -> Z)
               (prefix_sum_product_int_range: list Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_8 */

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

int *sum_product(int *numbers, int numbers_size)
/*@ With lv (numbers0: Z) (numbers_size0: Z)
    Require
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        0 <= numbers_size0 && numbers_size0 < INT_MAX &&
        problem_8_pre &&
        list_int_range(lv) &&
        prefix_sum_product_int_range(lv, numbers_size0) &&
        IntArray::full(numbers, numbers_size, lv)
    Ensure
        exists s p,
        __return != 0 &&
        problem_8_spec(lv, s, p) &&
        IntArray::full(numbers0, numbers_size0, lv) *
        IntArray::full(__return, 2, cons(s, cons(p, nil)))
*/
{
    int sum = 0;
    int product = 1;
    int i;
    int *out = malloc_int_array(2);

    /*@ Inv Assert
        numbers == numbers0 &&
        numbers_size == numbers_size0 &&
        out != 0 &&
        0 <= i && i <= numbers_size0 &&
        sum == prefix_sum(lv, i) &&
        product == prefix_product(lv, i) &&
        prefix_sum_product_int_range(lv, numbers_size0) &&
        IntArray::full(numbers, numbers_size, lv) *
        IntArray::undef_full(out, 2)
    */
    for (i = 0; i < numbers_size; i++) {
        sum += numbers[i];
        product *= numbers[i];
    }

    out[0] = sum;
    out[1] = product;
    return out;
}
