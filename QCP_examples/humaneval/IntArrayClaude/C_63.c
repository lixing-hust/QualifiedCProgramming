/*
The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fibfib(0) == 0
fibfib(1) == 0
fibfib(2) == 1
fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
Please write a function to efficiently compute the n-th element of the fibfib number sequence.
>>> fibfib(1)
0
>>> fibfib(5)
4
>>> fibfib(8)
24
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_63_pre_z: Z -> Prop)
               (problem_63_spec_z: Z -> Z -> Prop)
               (fibfib_z: Z -> Z)
               (fibfib_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import coins_63 */

int fibfib(int n)
/*@ Require
        0 <= n && n < 100 &&
        problem_63_pre_z(n) &&
        fibfib_step_int_range(n)
    Ensure
        problem_63_spec_z(n, __return) && emp
*/
{
    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 0;
    }
    if (n == 2) {
        return 1;
    }

    int a = 0;
    int b = 0;
    int c = 1;
    int next;
    int i;

    /*@ Inv Assert
        n == n@pre &&
        3 <= i && i <= n + 1 &&
        3 <= n &&
        n < 100 &&
        problem_63_pre_z(n) &&
        fibfib_step_int_range(n) &&
        a == fibfib_z(i - 3) &&
        b == fibfib_z(i - 2) &&
        c == fibfib_z(i - 1) &&
        undef_data_at(&next)
    */
    for (i = 3; i <= n; i++) {
        next = a + b + c;
        a = b;
        b = c;
        c = next;
    }
    return c;
}
