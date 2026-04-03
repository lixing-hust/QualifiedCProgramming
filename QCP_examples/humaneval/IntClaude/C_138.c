/*
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
is_equal_to_sum_even(4) == false
is_equal_to_sum_even(6) == false
is_equal_to_sum_even(8) == true
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_138_pre: Z -> Prop) */
/*@ Extern Coq (problem_138_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_138 */
int is_equal_to_sum_even(int n)
/*@ Require
        INT_MIN <= n && n <= INT_MAX && emp
    Ensure
        problem_138_spec_z(n@pre, __return) && emp
*/
{
    if (n%2==0 && n>=8) return 1;
    return 0;
}
