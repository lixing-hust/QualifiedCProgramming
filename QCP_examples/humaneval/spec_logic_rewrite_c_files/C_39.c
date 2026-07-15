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
#include "verification_stdlib.h"

/*@ Extern Coq (problem_39_pre_z: Z -> Prop)
               (problem_39_spec_z: Z -> Z -> Prop)
               (prime_fib_safe_z: Z -> Prop)
               (pf_loop_state_z: Z -> Z -> Z -> Prop)
               (pf_after_advance_z: Z -> Z -> Z -> Prop)
               (prime_scan_state_z: Z -> Z -> Z -> Prop)
               (finite_prime_candidate_z: Z -> Prop) */
/*@ Import Coq Require Import coins_39 */

int prime_fib(int n)
/*@ Require
        1 <= n && n <= 5 &&
        n < INT_MAX &&
        problem_39_pre_z(n) &&
        prime_fib_safe_z(n) && emp
    Ensure
        problem_39_spec_z(n@pre, __return) && emp
*/
{
    int f1,f2;
    f1=1;f2=2;
    int count=0;
    /*@ Inv Assert
        n == n@pre &&
        1 <= n && n <= 5 &&
        n < INT_MAX &&
        problem_39_pre_z(n) &&
        prime_fib_safe_z(n) &&
        0 <= count && count <= n &&
        pf_loop_state_z(count, f1, f2) &&
        ((count == n) => finite_prime_candidate_z(f1))
    */
    while (count<n)
    {
        f1=f1+f2;
        int m;
        m=f1;f1=f2;f2=m;
        /*@ Assert
            n == n@pre &&
            1 <= n && n <= 5 &&
            n < INT_MAX &&
            problem_39_pre_z(n) &&
            prime_fib_safe_z(n) &&
            0 <= count && count < n &&
            pf_after_advance_z(count, f1, f2) &&
            2 <= f1 && f1 <= 89 &&
            f2 <= 144 &&
            m == f2
        */
        int isprime=1;
        int w;
        /*@ Inv Assert
            n == n@pre &&
            1 <= n && n <= 5 &&
            n < INT_MAX &&
            problem_39_pre_z(n) &&
            prime_fib_safe_z(n) &&
            0 <= count && count < n &&
            pf_after_advance_z(count, f1, f2) &&
            2 <= f1 && f1 <= 89 &&
            m == f2 &&
            2 <= w && w <= 10 &&
            (isprime == 0 || isprime == 1) &&
            prime_scan_state_z(f1, w, isprime)
        */
        for (w=2; w <= f1 / w && w < 10; w++)
            if (f1%w==0)
            {
             isprime=0; break;
            }
        /*@ Assert
            n == n@pre &&
            1 <= n && n <= 5 &&
            n < INT_MAX &&
            problem_39_pre_z(n) &&
            prime_fib_safe_z(n) &&
            0 <= count && count < n &&
            pf_after_advance_z(count, f1, f2) &&
            2 <= f1 && f1 <= 89 &&
            m == f2 &&
            2 <= w && w <= 10 &&
            (isprime == 0 || isprime == 1) &&
            ((isprime != 0) => finite_prime_candidate_z(f1)) &&
            ((isprime == 0) => (! finite_prime_candidate_z(f1)))
        */
        if (isprime) count+=1;
        /*@ Assert
            n == n@pre &&
            1 <= n && n <= 5 &&
            n < INT_MAX &&
            problem_39_pre_z(n) &&
            prime_fib_safe_z(n) &&
            0 <= count && count <= n &&
            m == f2 &&
            2 <= w && w <= 10 &&
            (isprime == 0 || isprime == 1) &&
            pf_loop_state_z(count, f1, f2) &&
            ((count == n) => finite_prime_candidate_z(f1))
        */
        if (count==n) return f1;
    }
    return f1;
}
