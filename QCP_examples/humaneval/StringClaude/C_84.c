/*
Given a positive integer N, return the total sum of its digits in binary.

Example
    For N = 1000, the sum of digits will be 1 the output should be "1".
    For N = 150, the sum of digits will be 6 the output should be "110".
    For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
    @N integer
         Constraints: 0 <= N <= 10000.
Output:
     a string of binary number
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_84_pre_z: Z -> Prop)
               (problem_84_spec_z: Z -> list Z -> Prop)
               (decimal_sum_state_z: Z -> Z -> Z -> Prop)
               (decimal_sum_value_z: Z -> Z -> Prop)
               (binary_digits_z: Z -> list Z)
               (binary_count_state_z: Z -> Z -> Z -> Prop)
               (binary_fill_full_state_z: Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_84 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* solve(int N)
/*@ Require
        0 <= N && N <= 10000 &&
        problem_84_pre_z(N)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_84_spec_z(N, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (N == 0) {
        char *out_zero = malloc_char_array(2);
        out_zero[0] = 48;
        out_zero[1] = 0;
        return out_zero;
    } else {
        int origN = N;
        int x = N;
        int sum = 0;
        int num = 0;
        int orig = 0;
        int bits = 0;
        int t = 0;
        int total = 0;
        int i = 0;
        char *out = 0;

        /*@ Inv Assert
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            0 <= x && x <= N@pre &&
            0 <= sum && sum <= 10000 &&
            num == 0 &&
            orig == 0 &&
            bits == 0 &&
            t == 0 &&
            total == 0 &&
            i == 0 &&
            out == 0 &&
            decimal_sum_state_z(origN, x, sum)
        */
        while (x > 0) {
            sum = sum + (x % 10);
            x = x / 10;
        }

        /*@ Assert
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            x == 0 &&
            0 <= sum && sum <= 10000 &&
            num == 0 &&
            orig == 0 &&
            bits == 0 &&
            t == 0 &&
            total == 0 &&
            i == 0 &&
            out == 0 &&
            decimal_sum_value_z(origN, sum)
        */

        if (sum == 0) {
            char *out_zero = malloc_char_array(2);
            out_zero[0] = 48;
            out_zero[1] = 0;
            return out_zero;
        }

        num = sum;
        orig = num;
        t = num;

        /*@ Inv Assert
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            x == 0 &&
            sum == orig &&
            decimal_sum_value_z(origN, sum) &&
            orig == num &&
            0 < num && num <= 10000 &&
            0 <= t &&
            0 <= bits && bits < INT_MAX &&
            total == 0 &&
            i == 0 &&
            out == 0 &&
            binary_count_state_z(num, t, bits)
        */
        while (t > 0) {
            bits = bits + 1;
            t = t / 2;
        }

        total = bits;
        out = malloc_char_array(total + 1);

        /*@ Inv Assert
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            x == 0 &&
            sum == orig &&
            decimal_sum_value_z(origN, sum) &&
            orig == num &&
            0 < num && num <= 10000 &&
            t == 0 &&
            total == Zlength(binary_digits_z(num)) &&
            bits == total &&
            0 <= i && i <= total + 1 &&
            CharArray::full(out, i, repeat_Z(0, i)) *
            CharArray::undef_seg(out, i, total + 1)
        */
        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }

        /*@ Assert
            exists out_l,
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            x == 0 &&
            sum == orig &&
            decimal_sum_value_z(origN, sum) &&
            orig == num &&
            0 < num && num <= 10000 &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(binary_digits_z(num)) &&
            bits == total &&
            Zlength(out_l) == total &&
            binary_fill_full_state_z(num, num, bits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */

        /*@ Inv Assert
            exists out_l,
            N == N@pre &&
            origN == N@pre &&
            0 < N@pre && N@pre <= 10000 &&
            x == 0 &&
            sum == orig &&
            decimal_sum_value_z(origN, sum) &&
            0 < orig && orig <= 10000 &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(binary_digits_z(orig)) &&
            0 <= bits && bits <= total &&
            0 <= num &&
            Zlength(out_l) == total &&
            binary_fill_full_state_z(orig, num, bits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */
        while (num > 0) {
            bits = bits - 1;
            /*@ Assert
                exists out_l,
                N == N@pre &&
                origN == N@pre &&
                0 < N@pre && N@pre <= 10000 &&
                x == 0 &&
                sum == orig &&
                decimal_sum_value_z(origN, sum) &&
                0 < orig && orig <= 10000 &&
                0 < num &&
                t == 0 &&
                i == total + 1 &&
                total == Zlength(binary_digits_z(orig)) &&
                0 <= bits && bits < total &&
                Zlength(out_l) == total &&
                binary_fill_full_state_z(orig, num, bits + 1, out_l) &&
                CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
            */
            out[bits] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
