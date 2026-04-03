/*
Write a function that returns 1 if the object q will fly, && 0 otherwise.
The object q will fly if it's balanced (it is a palindromic vector) && the sum of its elements
is less than || equal the maximum possible weight w.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int will_it_fly(int *q, int q_size, int w)
/*@ With lv
    Require
        0 <= q_size && q_size < INT_MAX &&
        IntArray::full(q, q_size, lv)
    Ensure
        ((__return != 0) &&
         (forall (k: Z), (0 <= k && k < q_size) => Znth(k, lv, 0) == Znth(q_size - 1 - k, lv, 0)) &&
         sum(lv) <= w ||
         (__return == 0) &&
         ((exists k, 0 <= k && k < q_size && Znth(k, lv, 0) != Znth(q_size - 1 - k, lv, 0)) ||
          ((forall (k: Z), (0 <= k && k < q_size) => Znth(k, lv, 0) == Znth(q_size - 1 - k, lv, 0)) &&
           sum(lv) > w))) &&
        IntArray::full(q, q_size, lv)
*/
{
    int s = 0;
    int i;
    /*@ Inv
        0 <= i && i <= q_size@pre &&
        s == sum(sublist(0, i, lv)) &&
        (forall (k: Z), (0 <= k && k < i) => Znth(k, lv, 0) == Znth(q_size@pre - 1 - k, lv, 0)) &&
        IntArray::full(q, q_size@pre, lv)
    */
    for (i = 0; i < q_size; i++) {
        if (q[i] != q[q_size - 1 - i]) return 0;
        s += q[i];
    }
    if (s > w) return 0;
    return 1;
}
