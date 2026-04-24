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
               (largest_prime_prefix: Z -> list Z -> Z -> Prop)
               (prime_scan_state: Z -> Z -> Z -> Prop)
               (digit_sum_state: Z -> Z -> Z -> Prop)
               (list_nonneg_int_range: list Z -> Prop)
               (digit_sum_int_range: Z -> Prop) */
/*@ Import Coq Require Import coins_94 */

int skjkasdkd(int* lst, int lst_size)
/*@ With lv
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_94_pre_z(lv) &&
        list_nonneg_int_range(lv) &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        problem_94_spec_z(lv, __return) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int largest=0;
    int i;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_94_pre_z(lv) &&
        list_nonneg_int_range(lv) &&
        0 <= i && i <= lst_size &&
        largest_prime_prefix(i, lv, largest) &&
        digit_sum_int_range(largest) &&
        IntArray::full(lst, lst_size, lv)
    */
    for (i=0;i<lst_size;i++) {
        if (lst[i]>largest && lst[i]>1)
        {
            int x = lst[i];
            int prime=1;
            int j;

            /*@ Inv Assert
                lst == lst@pre &&
                lst_size == lst_size@pre &&
                0 <= lst_size && lst_size < INT_MAX &&
                lst_size == Zlength(lv) &&
                problem_94_pre_z(lv) &&
                list_nonneg_int_range(lv) &&
                0 <= i && i < lst_size &&
                x == Znth(i, lv, 0) &&
                x > largest &&
                x > 1 &&
                largest_prime_prefix(i, lv, largest) &&
                digit_sum_int_range(largest) &&
                2 <= j && j <= x + 1 &&
                0 <= prime && prime <= 1 &&
                prime_scan_state(x, j, prime) &&
                IntArray::full(lst, lst_size, lv)
            */
            for (j=2;j<=x/j;j++)
                if (x%j==0) prime=0;
            if (prime) largest=x;
        }
    }
    int sum=0;

    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_94_pre_z(lv) &&
        list_nonneg_int_range(lv) &&
        i == lst_size &&
        (exists original_largest,
            largest_prime_prefix(lst_size, lv, original_largest) &&
            digit_sum_int_range(original_largest) &&
            digit_sum_state(original_largest, largest, sum)) &&
        IntArray::full(lst, lst_size, lv)
    */
    while (largest > 0) {
        sum += largest % 10;
        largest /= 10;
    }
    return sum;
}
