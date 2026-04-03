/*
Return 1 if all numbers in the vector l are below threshold t, 0 otherwise.
>>> below_threshold({1, 2, 4, 10}, 100)
1
>>> below_threshold({1, 20, 4, 10}, 5)
0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int below_threshold(int *l, int l_size, int t)
/*@ With lv
    Require
        0 <= l_size && l_size < INT_MAX &&
        IntArray::full(l, l_size, lv)
    Ensure
        ((__return != 0) && (forall (k: Z), (0 <= k && k < l_size) => Znth(k, lv, 0) < t) ||
         (__return == 0) && (exists k, 0 <= k && k < l_size && Znth(k, lv, 0) >= t)) &&
        IntArray::full(l, l_size, lv)
*/
{
    int i;
    /*@ Inv
        0 <= i && i <= l_size@pre &&
        (forall (k: Z), (0 <= k && k < i) => Znth(k, lv, 0) < t) &&
        IntArray::full(l, l_size@pre, lv)
    */
    for (i = 0; i < l_size; i++)
        if (l[i] >= t) return 0;
    return 1;
}
