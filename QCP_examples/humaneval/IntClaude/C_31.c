/*
Return true if a given number is prime, && false otherwise.
>>> is_prime(6)
false
>>> is_prime(101)
true
>>> is_prime(11)
true
>>> is_prime(13441)
true
>>> is_prime(61)
true
>>> is_prime(4)
false
>>> is_prime(1)
false
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_31_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_31 */
int is_prime(int n)
/*@ Require
        0 <= n && n <= INT_MAX && emp
    Ensure
        problem_31_spec_z(n@pre, __return) && emp
*/
{
    if (n<2) return 0;
    int i;
    /*@ Inv
        2 <= i && i * i <= n@pre + 1 &&
        forall (k: Z), 2 <= k && k < i => n@pre % k != 0
    */
    for (i=2;i*i<=n;i++)
        if (n%i==0) return 0;
    return 1;
}
