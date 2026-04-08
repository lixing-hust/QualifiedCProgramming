/*
The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial(4)
288

The function will receive an integer as input && should return the special
factorial of this integer.
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (factorial: Z -> Z)
               (bfact_coq: Z -> Z) */
/*@ Extern Coq (problem_139_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_139_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_139 */
long long special_factorial(int n)
/*@ Require
        problem_139_pre_z(n) &&
        1 <= n && n <= 8 && emp
    Ensure
        problem_139_spec_z(n@pre, __return) && emp
*/
{
    long long fact=1,bfact=1;
    int i;
    /*@ Inv
        1 <= i && i <= n@pre + 1 &&
        fact == factorial(i - 1) &&
        bfact == bfact_coq(i - 1)
    */
    for (i=1;i<=n;i++)
    {
        fact=fact*i;
        bfact=bfact*fact;
    }
    return bfact;
}
