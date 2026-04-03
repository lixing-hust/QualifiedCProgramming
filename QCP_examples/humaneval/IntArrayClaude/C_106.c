/*
Compute a sequence of size n: element at 1-indexed position i is
  factorial(i) if i is even, or triangular(i) = 1+2+...+i if i is odd.
Output is written into pre-allocated array out of size n.
f(5) == {1, 2, 6, 24, 15}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (f_seq: Z -> list Z) */

void f(int n, int *out)
/*@ Require
        1 <= n && n < INT_MAX &&
        IntArray::undef_full(out, n)
    Ensure
        IntArray::full(out, n, f_seq(n))
*/
{
    int s = 0;
    int p = 1;
    int i;
    /*@ Inv
        0 <= i && i <= n@pre &&
        IntArray::seg(out@pre, 0, i, sublist(0, i, f_seq(n@pre))) *
        IntArray::undef_seg(out@pre, i, n@pre)
    */
    for (i = 0; i < n; i++) {
        s += (i + 1);
        p *= (i + 1);
        if ((i + 1) % 2 == 0) out[i] = p;
        else out[i] = s;
    }
}
