/*
Return vector with elements incremented by 1.
Output is written into pre-allocated array `out` of the same size.
>>> incr_list({1, 2, 3}, out)
out = {2, 3, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (map_incr: list Z -> list Z) */

void incr_list(int *l, int l_size, int *out)
/*@ With lv
    Require
        0 <= l_size && l_size < INT_MAX &&
        IntArray::full(l, l_size, lv) *
        IntArray::undef_full(out, l_size)
    Ensure
        IntArray::full(l, l_size, lv) *
        IntArray::full(out, l_size, map_incr(lv))
*/
{
    int i;
    /*@ Inv
        0 <= i && i <= l_size@pre &&
        IntArray::full(l, l_size@pre, lv) *
        IntArray::seg(out@pre, 0, i, map_incr(sublist(0, i, lv))) *
        IntArray::undef_seg(out@pre, i, l_size@pre)
    */
    for (i = 0; i < l_size; ++i)
        out[i] = l[i] + 1;
}
