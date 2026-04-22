/*
triples_sum_to_zero takes a vector of integers as an input.
it returns true if there are three distinct elements in the vector that
sum to zero, && false otherwise.

>>> triples_sum_to_zero({1, 3, 5, 0})
false
>>> triples_sum_to_zero({1, 3, -2, 1})
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_40_pre: list Z -> Prop)
               (problem_40_spec: list Z -> bool -> Prop)
               (triple_sum_int_range: list Z -> Z -> Prop)
               (scanned_i: list Z -> Z -> Z -> Prop)
               (scanned_j: list Z -> Z -> Z -> Z -> Prop)
               (scanned_k: list Z -> Z -> Z -> Z -> Z -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import coins_40 */

int triples_sum_to_zero(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        problem_40_pre(input_l) &&
        triple_sum_int_range(input_l, l_size) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        ((__return != 0) && problem_40_spec(input_l, true) ||
         (__return == 0) && problem_40_spec(input_l, false)) &&
        IntArray::full(l, l_size, input_l)
*/
{
    int i;
    int j;
    int k;
    /*@ Inv Assert
        l == l@pre &&
        l_size == l_size@pre &&
        0 <= i && i <= l_size@pre &&
        triple_sum_int_range(input_l, l_size@pre) &&
        scanned_i(input_l, l_size@pre, i) &&
        undef_data_at(&j) *
        undef_data_at(&k) *
        IntArray::full(l@pre, l_size@pre, input_l)
    */
    for (i = 0; i < l_size; i++) {
        /*@ Inv Assert
            l == l@pre &&
            l_size == l_size@pre &&
            0 <= i && i < l_size@pre &&
            i + 1 <= j && j <= l_size@pre &&
            triple_sum_int_range(input_l, l_size@pre) &&
            scanned_j(input_l, l_size@pre, i, j) &&
            undef_data_at(&k) *
            IntArray::full(l@pre, l_size@pre, input_l)
        */
        for (j = i + 1; j < l_size; j++) {
            /*@ Inv Assert
                l == l@pre &&
                l_size == l_size@pre &&
                0 <= i && i < j &&
                j < l_size@pre &&
                j + 1 <= k && k <= l_size@pre &&
                triple_sum_int_range(input_l, l_size@pre) &&
                scanned_k(input_l, l_size@pre, i, j, k) &&
                IntArray::full(l@pre, l_size@pre, input_l)
            */
            for (k = j + 1; k < l_size; k++)
                if (l[i] + l[j] + l[k] == 0) return 1;
        }
    }
    return 0;
}
