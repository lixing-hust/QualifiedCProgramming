/*
A simple program which should return the value of x if n is
a prime number && should return the value of y otherwise.

Examples:
for x_or_y(7, 34, 12) == 34
for x_or_y(15, 8, 5) == 5

*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_150_spec_z: Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_150 */
int x_or_y(int n, int x, int y)
/*@ Require
        2 <= n && n <= INT_MAX &&
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= y && y <= INT_MAX && emp
    Ensure
        problem_150_spec_z(n@pre, x@pre, y@pre, __return) && emp
*/
{
    int isp=1;
    if (n<2) isp=0;
    int i;
    /*@ Inv
        2 <= i && i <= n@pre &&
        (isp != 0 => forall (k: Z), 2 <= k && k < i => n@pre % k != 0)
    */
    for (i=2;i*i<=n;i++)
    if (n%i==0) isp=0;
    if (isp) return x;
    return y;
}
