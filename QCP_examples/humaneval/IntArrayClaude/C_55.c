/*
Return n-th Fibonacci number (1-indexed: fib(1)=1, fib(2)=1, fib(3)=2, ...).
Rewritten to avoid local arrays: uses two rolling variables.
>>> fib(10) = 55
>>> fib(1)  = 1
>>> fib(8)  = 21
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_55_pre_z: Z -> Prop)
               (problem_55_spec_z: Z -> Z -> Prop)
               (fib_seq: Z -> Z)
               (fib_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import coins_55 */

int fib(int n)
/*@ Require
        1 <= n && n < 100 &&
        problem_55_pre_z(n) &&
        fib_step_int_range(n) && emp
    Ensure problem_55_spec_z(n, __return) && emp
*/
{
    int a;
    int b;
    int c;
    int i;
    a = 0;
    b = 1;
    /*@ Inv Assert
        n == n@pre &&
        2 <= i && i <= n@pre + 1 &&
        1 <= n@pre && n@pre < 100 &&
        problem_55_pre_z(n@pre) &&
        fib_step_int_range(n@pre) &&
        a == fib_seq(i - 2) &&
        b == fib_seq(i - 1) &&
        undef_data_at(&c)
    */
    for (i = 2; i <= n; i++) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}
