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
#include "verification_stdlib.h"

/*@ Extern Coq (problem_139_pre_z: Z -> Prop)
               (problem_139_spec_z: Z -> Z -> Prop)
               (special_factorial_safe_z: Z -> Prop)
               (factorial_z: Z -> Z)
               (bfact_z: Z -> Z) */
/*@ Import Coq Require Import coins_139 */

long long special_factorial(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        1 <= n0 && n0 <= 8 &&
        problem_139_pre_z(n0) &&
        special_factorial_safe_z(n0) && emp
    Ensure
        problem_139_spec_z(n0, __return) && emp
*/
{
    long long fact=1,bfact=1;
    /*@ Inv Assert
        n == n0 &&
        1 <= n0 && n0 <= 8 &&
        problem_139_pre_z(n0) &&
        special_factorial_safe_z(n0) &&
        1 <= i && i <= n0 + 1 &&
        1 <= fact && fact <= 9223372036854775807 &&
        1 <= bfact && bfact <= 9223372036854775807 &&
        fact == factorial_z(i - 1) &&
        bfact == bfact_z(i - 1)
    */
    for (int i=1;i<=n;i++)
    {
        fact=fact*i;
        bfact=bfact*fact;
    }
    return bfact;
}
