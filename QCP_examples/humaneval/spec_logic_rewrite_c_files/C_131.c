/*
Given a positive integer n, return the product of the odd digits.
Return 0 if all digits are even.
For example:
digits(1)  == 1
digits(4)  == 0
digits(235) == 15
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_131_pre_z: Z -> Prop)
               (problem_131_spec_z: Z -> Z -> Prop)
               (digits_product_safe_z: Z -> Prop)
               (digits_state_z: Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_131 */

int digits(int n)
/*@ Require
        0 < n && n < INT_MAX &&
        problem_131_pre_z(n) &&
        digits_product_safe_z(n) && emp
    Ensure
        problem_131_spec_z(n@pre, __return) && emp
*/
{
    int prod=1,has=0;
    if (n == 0) return 0;
    /*@ Inv Assert
        0 < n@pre && n@pre < INT_MAX &&
        problem_131_pre_z(n@pre) &&
        digits_product_safe_z(n@pre) &&
        0 <= n && n <= n@pre &&
        0 <= prod && prod <= INT_MAX &&
        (has == 0 || has == 1) &&
        digits_state_z(n@pre, n, prod, has)
    */
    while (n > 0) {
        int d = n % 10;
        if (d % 2 == 1) {
            has = 1;
            prod *= d;
        }
        n /= 10;
    }
    if (has==0) return 0;
    return prod;
}
