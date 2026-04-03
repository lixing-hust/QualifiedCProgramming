/*
Your task is to write a function that returns true if a number x is a simple
power of n && false in other cases.
x is a simple power of n if n**int=x
For example:
is_simple_power(1, 4) => true
is_simple_power(2, 2) => true
is_simple_power(8, 2) => true
is_simple_power(3, 2) => false
is_simple_power(3, 1) => false
is_simple_power(5, 3) => false
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_76_pre: Z -> Z -> Prop) */
/*@ Extern Coq (is_simple_power_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_76 */
int is_simple_power(int x, int n)
/*@ Require
        1 <= x && x <= INT_MAX &&
        1 <= n && n <= INT_MAX && emp
    Ensure
        is_simple_power_spec(x@pre, n@pre, __return) && emp
*/
{
    int p=1,count=0;
    /*@ Inv
        1 <= p && 0 <= count && count <= 100 &&
        (count == 0 => p == 1)
    */
    while (p<=x && count<100)
    {
        if (p==x) return 1;
        p=p*n;count+=1;
    }
    return 0;
}
