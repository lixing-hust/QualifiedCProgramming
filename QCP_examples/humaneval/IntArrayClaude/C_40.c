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

int triples_sum_to_zero(int *l, int l_size)
/*@ With lv
    Require
        0 <= l_size && l_size < INT_MAX &&
        IntArray::full(l, l_size, lv)
    Ensure
        ((__return != 0) &&
         (exists p, exists q, exists r,
          0 <= p && p < q && q < r && r < l_size &&
          Znth(p, lv, 0) + Znth(q, lv, 0) + Znth(r, lv, 0) == 0) ||
         (__return == 0) &&
         (forall (p: Z) (q: Z) (r: Z),
          (0 <= p && p < q && q < r && r < l_size) =>
          Znth(p, lv, 0) + Znth(q, lv, 0) + Znth(r, lv, 0) != 0)) &&
        IntArray::full(l, l_size, lv)
*/
{
    int i;
    int j;
    int k;
    /*@ Inv
        0 <= i && i <= l_size@pre &&
        (forall (p: Z) (q: Z) (r: Z),
         (0 <= p && p < i && p < q && q < r && r < l_size@pre) =>
         Znth(p, lv, 0) + Znth(q, lv, 0) + Znth(r, lv, 0) != 0) &&
        IntArray::full(l, l_size@pre, lv)
    */
    for (i = 0; i < l_size; i++) {
        /*@ Inv
            0 <= i && i < l_size@pre &&
            i + 1 <= j && j <= l_size@pre &&
            (forall (q: Z) (r: Z),
             (i + 1 <= q && q < j && q < r && r < l_size@pre) =>
             Znth(i, lv, 0) + Znth(q, lv, 0) + Znth(r, lv, 0) != 0) &&
            IntArray::full(l, l_size@pre, lv)
        */
        for (j = i + 1; j < l_size; j++) {
            /*@ Inv
                0 <= i && i < l_size@pre &&
                0 <= j && j < l_size@pre &&
                j + 1 <= k && k <= l_size@pre &&
                (forall (r: Z), (j + 1 <= r && r < k) =>
                 Znth(i, lv, 0) + Znth(j, lv, 0) + Znth(r, lv, 0) != 0) &&
                IntArray::full(l, l_size@pre, lv)
            */
            for (k = j + 1; k < l_size; k++)
                if (l[i] + l[j] + l[k] == 0) return 1;
        }
    }
    return 0;
}
