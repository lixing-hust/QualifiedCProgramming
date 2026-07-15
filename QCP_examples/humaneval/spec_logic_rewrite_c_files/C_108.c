/*
Write a function count_nums which takes a vector of integers && returns
the number of elements which has a digit_sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, && 3.
>>> count_nums({}) == 0
>>> count_nums({-1, 11, -11}) == 1
>>> count_nums({1, 1, 2}) == 3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_108_pre_z: list Z -> Prop)
               (problem_108_spec_z: list Z -> Z -> Prop)
               (count_nums_safe_108: list Z -> Prop)
               (count_nums_prefix_108: list Z -> Z -> Z -> Prop)
               (signed_digit_sum_state_108: Z -> Z -> Z -> Prop)
               (signed_digit_sum_positive_108: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_108 */

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

int count_nums(int* n, int n_size)
/*@ With input_l
    Require
        n != 0 &&
        0 <= n_size && n_size < INT_MAX &&
        n_size == Zlength(input_l) &&
        problem_108_pre_z(input_l) &&
        count_nums_safe_108(input_l) &&
        IntArray::full(n, n_size, input_l)
    Ensure
        problem_108_spec_z(input_l, __return) &&
        IntArray::full(n, n_size, input_l)
*/
{
    int num=0;
    int i;
    /*@ Inv Assert
        n == n@pre &&
        n_size == n_size@pre &&
        0 <= n_size && n_size < INT_MAX &&
        n_size == Zlength(input_l) &&
        problem_108_pre_z(input_l) &&
        count_nums_safe_108(input_l) &&
        0 <= i && i <= n_size &&
        0 <= num && num <= i &&
        count_nums_prefix_108(input_l, i, num) &&
        IntArray::full(n, n_size, input_l)
    */
    for (i=0;i<n_size;i++) {
        int current = n[i];
        /*@ Assert
            n == n@pre &&
            n_size == n_size@pre &&
            0 <= n_size && n_size < INT_MAX &&
            n_size == Zlength(input_l) &&
            problem_108_pre_z(input_l) &&
            count_nums_safe_108(input_l) &&
            0 <= i && i < n_size &&
            0 <= num && num <= i &&
            current == Znth(i, input_l, 0) &&
            INT_MIN < current && current <= INT_MAX &&
            count_nums_prefix_108(input_l, i, num) &&
            IntArray::full(n, n_size, input_l)
        */
        if (current>0) {
            num+=1;
            /*@ Assert
                n == n@pre &&
                n_size == n_size@pre &&
                0 <= n_size && n_size < INT_MAX &&
                n_size == Zlength(input_l) &&
                problem_108_pre_z(input_l) &&
                count_nums_safe_108(input_l) &&
                0 <= i && i < n_size &&
                0 <= num && num <= i + 1 &&
                current == Znth(i, input_l, 0) &&
                current > 0 &&
                count_nums_prefix_108(input_l, i + 1, num) &&
                IntArray::full(n, n_size, input_l)
            */
        } else {
            int digit_sum=0;
            int w=abs(current);
            /*@ Assert
                n == n@pre &&
                n_size == n_size@pre &&
                0 <= n_size && n_size < INT_MAX &&
                n_size == Zlength(input_l) &&
                problem_108_pre_z(input_l) &&
                count_nums_safe_108(input_l) &&
                0 <= i && i < n_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                INT_MIN < current && current <= 0 &&
                w == Zabs(current) &&
                0 <= w && w <= INT_MAX &&
                digit_sum == 0 &&
                signed_digit_sum_state_108(current, w, digit_sum) &&
                count_nums_prefix_108(input_l, i, num) &&
                IntArray::full(n, n_size, input_l)
            */
            /*@ Inv Assert
                n == n@pre &&
                n_size == n_size@pre &&
                0 <= n_size && n_size < INT_MAX &&
                n_size == Zlength(input_l) &&
                problem_108_pre_z(input_l) &&
                count_nums_safe_108(input_l) &&
                0 <= i && i < n_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                INT_MIN < current && current <= 0 &&
                0 <= w && w <= INT_MAX &&
                INT_MIN < digit_sum && digit_sum < INT_MAX &&
                signed_digit_sum_state_108(current, w, digit_sum) &&
                count_nums_prefix_108(input_l, i, num) &&
                IntArray::full(n, n_size, input_l)
            */
            while (w>=10)
            {
                digit_sum+=w%10;
                w=w/10;
            }
            digit_sum-=w;
            /*@ Assert
                n == n@pre &&
                n_size == n_size@pre &&
                0 <= n_size && n_size < INT_MAX &&
                n_size == Zlength(input_l) &&
                problem_108_pre_z(input_l) &&
                count_nums_safe_108(input_l) &&
                0 <= i && i < n_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                INT_MIN < current && current <= 0 &&
                INT_MIN < digit_sum && digit_sum < INT_MAX &&
                signed_digit_sum_positive_108(current, digit_sum) &&
                count_nums_prefix_108(input_l, i, num) &&
                IntArray::full(n, n_size, input_l) *
                data_at(&w, w)
            */
            if (digit_sum>0) {
                num+=1;
                /*@ Assert
                    n == n@pre &&
                    n_size == n_size@pre &&
                    0 <= n_size && n_size < INT_MAX &&
                    n_size == Zlength(input_l) &&
                    problem_108_pre_z(input_l) &&
                    count_nums_safe_108(input_l) &&
                    0 <= i && i < n_size &&
                    0 <= num && num <= i + 1 &&
                    current == Znth(i, input_l, 0) &&
                    current <= 0 &&
                    digit_sum > 0 &&
                    signed_digit_sum_positive_108(current, digit_sum) &&
                    count_nums_prefix_108(input_l, i + 1, num) &&
                    IntArray::full(n, n_size, input_l) *
                    data_at(&w, w)
                */
            } else {
                /*@ Assert
                    n == n@pre &&
                    n_size == n_size@pre &&
                    0 <= n_size && n_size < INT_MAX &&
                    n_size == Zlength(input_l) &&
                    problem_108_pre_z(input_l) &&
                    count_nums_safe_108(input_l) &&
                    0 <= i && i < n_size &&
                    0 <= num && num <= i &&
                    current == Znth(i, input_l, 0) &&
                    current <= 0 &&
                    digit_sum <= 0 &&
                    signed_digit_sum_positive_108(current, digit_sum) &&
                    count_nums_prefix_108(input_l, i + 1, num) &&
                    IntArray::full(n, n_size, input_l) *
                    data_at(&w, w)
                */
            }
        }
    }
    return num;
}
