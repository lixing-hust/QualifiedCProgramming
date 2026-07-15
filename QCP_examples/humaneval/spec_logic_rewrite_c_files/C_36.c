/*
Return the number of times the digit 7 appears in integers less than n which are divisible by 11 || 13.
>>> fizz_buzz(50)
0
>>> fizz_buzz(78)
2
>>> fizz_buzz(79)
3
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_36_pre_z: Z -> Prop)
               (problem_36_spec_z: Z -> Z -> Prop)
               (fizz_buzz_prefix_z: Z -> Z)
               (fizz_buzz_prefix_safe_z: Z -> Prop)
               (count_digit7_z: Z -> Z)
               (divisible_11_or_13_z: Z -> Prop)
               (digit7_state_z: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_36 */

int fizz_buzz(int n)
/*@ Require
        0 <= n && n < INT_MAX &&
        problem_36_pre_z(n) &&
        fizz_buzz_prefix_safe_z(n) &&
        fizz_buzz_prefix_z(n) <= INT_MAX && emp
    Ensure
        problem_36_spec_z(n@pre, __return) && emp
*/
{
    int count=0;
    /*@ Inv Assert
        n == n@pre &&
        0 <= n && n < INT_MAX &&
        problem_36_pre_z(n) &&
        fizz_buzz_prefix_safe_z(n) &&
        fizz_buzz_prefix_z(n) <= INT_MAX &&
        0 <= i && i <= n &&
        count == fizz_buzz_prefix_z(i) &&
        count <= INT_MAX
    */
    for (int i=0;i<n;i++) {
        if (i%11==0 || i%13==0)
        {
            int q=i;
            int digit_count=0;
            /*@ Inv Assert
                n == n@pre &&
                0 <= n && n < INT_MAX &&
                problem_36_pre_z(n) &&
                fizz_buzz_prefix_safe_z(n) &&
                fizz_buzz_prefix_z(n) <= INT_MAX &&
                0 <= i && i < n &&
                divisible_11_or_13_z(i) &&
                0 <= q && q <= i &&
                0 <= digit_count &&
                digit_count <= count_digit7_z(i) &&
                count == fizz_buzz_prefix_z(i) + digit_count &&
                digit7_state_z(i, q, digit_count) &&
                count + count_digit7_z(q) <= INT_MAX &&
                digit_count + count_digit7_z(q) <= INT_MAX &&
                count <= INT_MAX
            */
            while (q>0)
            {
                if (q%10==7) {
                    count+=1;
                    digit_count+=1;
                }
                q=q/10;
            }
        }
        /*@ Assert
            n == n@pre &&
            0 <= n && n < INT_MAX &&
            problem_36_pre_z(n) &&
            fizz_buzz_prefix_safe_z(n) &&
            fizz_buzz_prefix_z(n) <= INT_MAX &&
            0 <= i && i < n &&
            count == fizz_buzz_prefix_z(i + 1) &&
            count <= INT_MAX
        */
    }
    return count;
}
