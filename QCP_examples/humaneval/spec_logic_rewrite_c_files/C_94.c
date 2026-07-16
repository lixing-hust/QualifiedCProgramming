/*
You are given a vector of integers.
You need to find the largest prime value && return the sum of its digits.

Examples:
For lst = {0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3} the output should be 10
For lst = {1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1} the output should be 25
For lst = {1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3} the output should be 13
For lst = {0,724,32,71,99,32,6,0,5,91,83,0,5,6} the output should be 11
For lst = {0,81,12,3,1,21} the output should be 3
For lst = {0,8,1,2,1,7} the output should be 7
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_94_pre_z: list Z -> Prop)
               (problem_94_spec_z: list Z -> Z -> Prop)
               (largest_prime_prefix_94: Z -> list Z -> Z)
               (prime_scan_state_94: Z -> Z -> Z -> Prop)
               (prime_flag_done_94: Z -> Z -> Z -> Prop)
               (digit_sum_state_94: Z -> Z -> Z -> Prop)
               (skjkasdkd_safe_94: list Z -> Prop) */
/*@ Import Coq Require Import coins_94 */

int skjkasdkd(int* lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_94_pre_z(input_l) &&
        skjkasdkd_safe_94(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_94_spec_z(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int largest = 0;
    int i = 0;
    int x = 0;
    int prime = 0;
    int j = 0;
    int sum = 0;
    int original = 0;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_94_pre_z(input_l) &&
        skjkasdkd_safe_94(input_l) &&
        0 <= i && i <= lst_size &&
        0 <= largest && largest <= 2147395599 &&
        largest == largest_prime_prefix_94(i, input_l) &&
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= prime && prime <= INT_MAX &&
        INT_MIN <= j && j <= INT_MAX &&
        INT_MIN <= sum && sum <= INT_MAX &&
        INT_MIN <= original && original <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i = 0; i < lst_size; i++) {
        x = lst[i];
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            0 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_94_pre_z(input_l) &&
            skjkasdkd_safe_94(input_l) &&
            0 <= i && i < lst_size &&
            x == Znth(i, input_l, 0) &&
            INT_MIN <= x && x <= 2147395599 &&
            0 <= largest && largest <= 2147395599 &&
            largest == largest_prime_prefix_94(i, input_l) &&
            INT_MIN <= prime && prime <= INT_MAX &&
            INT_MIN <= j && j <= INT_MAX &&
            INT_MIN <= sum && sum <= INT_MAX &&
            INT_MIN <= original && original <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
        if (x > largest && x > 1) {
            prime = 1;
            /*@ Inv Assert
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                0 <= lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(input_l) &&
                problem_94_pre_z(input_l) &&
                skjkasdkd_safe_94(input_l) &&
                0 <= i && i < lst_size &&
                x == Znth(i, input_l, 0) &&
                2 <= x && x <= 2147395599 &&
                0 <= largest && largest < x &&
                largest == largest_prime_prefix_94(i, input_l) &&
                2 <= j && j <= x && j <= 46340 &&
                0 <= prime && prime <= 1 &&
                prime_scan_state_94(x, j, prime) &&
                INT_MIN <= sum && sum <= INT_MAX &&
                INT_MIN <= original && original <= INT_MAX &&
                IntArray::full(lst, lst_size, input_l)
            */
            for (j = 2; j * j <= x; j++) {
                if (x % j == 0) {
                    prime = 0;
                }
                /*@ Assert
                    lst == lst@pre &&
                    lst_size == lst_size@pre &&
                    0 <= lst_size && lst_size < INT_MAX &&
                    lst_size == Zlength(input_l) &&
                    problem_94_pre_z(input_l) &&
                    skjkasdkd_safe_94(input_l) &&
                    0 <= i && i < lst_size &&
                    x == Znth(i, input_l, 0) &&
                    2 <= x && x <= 2147395599 &&
                    0 <= largest && largest < x &&
                    largest == largest_prime_prefix_94(i, input_l) &&
                    j * j <= x &&
                    2 <= j && j <= x && j < 46340 &&
                    0 <= prime && prime <= 1 &&
                    prime_scan_state_94(x, j + 1, prime) &&
                    INT_MIN <= sum && sum <= INT_MAX &&
                    INT_MIN <= original && original <= INT_MAX &&
                    IntArray::full(lst, lst_size, input_l)
                */
            }
            /*@ Assert
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                0 <= lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(input_l) &&
                problem_94_pre_z(input_l) &&
                skjkasdkd_safe_94(input_l) &&
                0 <= i && i < lst_size &&
                x == Znth(i, input_l, 0) &&
                2 <= x && x <= 2147395599 &&
                0 <= largest && largest < x &&
                largest == largest_prime_prefix_94(i, input_l) &&
                2 <= j && j <= x && j <= 46340 &&
                j * j > x &&
                0 <= prime && prime <= 1 &&
                prime_flag_done_94(x, j, prime) &&
                INT_MIN <= sum && sum <= INT_MAX &&
                INT_MIN <= original && original <= INT_MAX &&
                IntArray::full(lst, lst_size, input_l)
            */
            if (prime == 1) {
                largest = x;
            }
        }
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            0 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_94_pre_z(input_l) &&
            skjkasdkd_safe_94(input_l) &&
            0 <= i && i < lst_size &&
            x == Znth(i, input_l, 0) &&
            INT_MIN <= x && x <= 2147395599 &&
            0 <= largest && largest <= 2147395599 &&
            largest == largest_prime_prefix_94(i + 1, input_l) &&
            INT_MIN <= prime && prime <= INT_MAX &&
            INT_MIN <= j && j <= INT_MAX &&
            INT_MIN <= sum && sum <= INT_MAX &&
            INT_MIN <= original && original <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }

    original = largest;
    sum = 0;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_94_pre_z(input_l) &&
        skjkasdkd_safe_94(input_l) &&
        i == lst_size &&
        original == largest_prime_prefix_94(lst_size, input_l) &&
        0 <= original && original <= 2147395599 &&
        0 <= largest && largest <= original &&
        0 <= sum && sum <= INT_MAX &&
        digit_sum_state_94(original, largest, sum) &&
        INT_MIN <= i && i <= INT_MAX &&
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= prime && prime <= INT_MAX &&
        INT_MIN <= j && j <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    while (largest > 0) {
        sum += largest % 10;
        largest /= 10;
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            0 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_94_pre_z(input_l) &&
            skjkasdkd_safe_94(input_l) &&
            i == lst_size &&
            original == largest_prime_prefix_94(lst_size, input_l) &&
            0 <= original && original <= 2147395599 &&
            0 <= largest && largest <= original &&
            0 <= sum && sum <= INT_MAX &&
            digit_sum_state_94(original, largest, sum) &&
            INT_MIN <= i && i <= INT_MAX &&
            INT_MIN <= x && x <= INT_MAX &&
            INT_MIN <= prime && prime <= INT_MAX &&
            INT_MIN <= j && j <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }
    return sum;
}
