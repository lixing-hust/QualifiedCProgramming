/*
Given a positive integer n, make a pile of n levels of stones.
Level i (0-indexed) has n + 2*i stones (always increments by 2).
Output is written into pre-allocated array out of size n.

>>> make_a_pile(3) => {3, 5, 7}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (make_pile: Z -> list Z) */

void make_a_pile(int n, int *out)
/*@ Require
        1 <= n && n < INT_MAX &&
        IntArray::undef_full(out, n)
    Ensure
        IntArray::full(out, n, make_pile(n))
*/
{
    int i;
    /*@ Inv
        0 <= i && i <= n@pre &&
        IntArray::seg(out@pre, 0, i, sublist(0, i, make_pile(n@pre))) *
        IntArray::undef_seg(out@pre, i, n@pre)
    */
    for (i = 0; i < n; i++)
        out[i] = n + 2 * i;
}
