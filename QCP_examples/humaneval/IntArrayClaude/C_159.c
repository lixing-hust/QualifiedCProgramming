/*
You"re a hungry rabbit, && you already have eaten a certain number of carrots,
but now you need to eat more carrots to complete the day's meals.
you should return a vector of { total number of eaten carrots after your meals,
                                the number of carrots left after your meals }
if there are ! enough remaining carrots, you will eat all remaining carrots, but will still be hungry.

Example:
* eat(5, 6, 10) -> {11, 4}
* eat(4, 8, 9) -> {12, 1}
* eat(1, 10, 10) -> {11, 0}
* eat(2, 11, 5) -> {7, 0}

Variables:
@number : integer
    the number of carrots that you have eaten.
@need : integer
    the number of carrots that you need to eat.
@remaining : integer
    the number of remaining carrots thet exist in stock

Constrain:
* 0 <= number <= 1000
* 0 <= need <= 1000
* 0 <= remaining <= 1000

Have fun :)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_159_pre_z: Z -> Z -> Z -> Prop)
               (problem_159_spec_z: Z -> Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_159 */

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

IntArray *eat(int number,int need,int remaining)
/*@ Require
        problem_159_pre_z(number, need, remaining)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == 2 &&
        output_size == Zlength(output_l) &&
        problem_159_spec_z(number, need, remaining, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    if (need>remaining) {
        data[0] = number + remaining;
        data[1] = 0;
        return out;
    }
    data[0] = number + need;
    data[1] = remaining - need;
    return out;
}
