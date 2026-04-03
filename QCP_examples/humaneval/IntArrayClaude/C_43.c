/*
pairs_sum_to_zero takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> pairs_sum_to_zero({1, 3, 5, 0})
false
>>> pairs_sum_to_zero({2, 4, -5, 3, 5, 7})
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int pairs_sum_to_zero(int *l, int l_size)
/*@ With lv
    Require
        0 <= l_size && l_size < INT_MAX &&
        IntArray::full(l, l_size, lv)
    Ensure
        ((__return != 0) &&
         (exists p, exists q, 0 <= p && p < q && q < l_size &&
          Znth(p, lv, 0) + Znth(q, lv, 0) == 0) ||
         (__return == 0) &&
         (forall (p: Z) (q: Z), (0 <= p && p < q && q < l_size) =>
          Znth(p, lv, 0) + Znth(q, lv, 0) != 0)) &&
        IntArray::full(l, l_size, lv)
*/
{
    int i;
    int j;
    /*@ Inv
        0 <= i && i <= l_size@pre &&
        (forall (p: Z) (q: Z), (0 <= p && p < i && p < q && q < l_size@pre) =>
         Znth(p, lv, 0) + Znth(q, lv, 0) != 0) &&
        IntArray::full(l, l_size@pre, lv)
    */
    for (i = 0; i < l_size; i++) {
        /*@ Inv
            0 <= i && i < l_size@pre &&
            i + 1 <= j && j <= l_size@pre &&
            (forall (q: Z), (i + 1 <= q && q < j) =>
             Znth(i, lv, 0) + Znth(q, lv, 0) != 0) &&
            IntArray::full(l, l_size@pre, lv)
        */
        for (j = i + 1; j < l_size; j++)
            if (l[i] + l[j] == 0) return 1;
    }
    return 0;
}
