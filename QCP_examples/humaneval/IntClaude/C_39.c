/*
prime_fib returns n-th number that is a Fibonacci number && it's also prime.
>>> prime_fib(1)
2
>>> prime_fib(2)
3
>>> prime_fib(3)
5
>>> prime_fib(4)
13
>>> prime_fib(5)
89
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (prime_fib_coq: Z -> Z) */
/*@ Extern Coq (problem_39_pre_z: Z -> Prop) */
/*@ Extern Coq (prime_fib_spec: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_39 */
int prime_fib(int n)
/*@ Require
        problem_39_pre_z(n) &&
        1 <= n && n <= 20 && emp
    Ensure
        prime_fib_spec(n@pre, __return) && emp
*/
{
    int f1,f2,m;
    f1=1;f2=2;
    int count=0;
    /*@ Inv
        0 <= count && count <= n@pre &&
        f1 >= 1 && f2 >= 1
    */
    while (count<n)
    {
        f1=f1+f2;
        m=f1;f1=f2;f2=m;
        int isprime=1;
        int w;
        /*@ Inv
            2 <= w && f1 >= 2 && (isprime != 0 => forall (k: Z), 2 <= k && k < w => f1 % k != 0)
        */
        for (w=2;w*w<=f1;w++)
            if (f1%w==0)
            {
             isprime=0; break;
            }
        if (isprime) count+=1;
        if (count==n) return f1;
    }
    return f2;
}
