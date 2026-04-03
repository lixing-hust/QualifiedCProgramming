/*
Return n-th Fibonacci number (1-indexed: fib(1)=1, fib(2)=1, fib(3)=2, ...).
Rewritten to avoid local arrays: uses two rolling variables.
>>> fib(10) = 55
>>> fib(1)  = 1
>>> fib(8)  = 21
*/
#include "verification_stdlib.h"

/*@ Extern Coq (fib_seq: Z -> Z) */

int fib(int n)
/*@ Require 1 <= n && emp
    Ensure __return == fib_seq(n) && emp
*/
{
    int a;
    int b;
    int c;
    int i;
    a = 0;
    b = 1;
    /*@ Inv
        2 <= i && i <= n@pre + 1 &&
        a == fib_seq(i - 2) &&
        b == fib_seq(i - 1) && emp
    */
    for (i = 2; i <= n; i++) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}
