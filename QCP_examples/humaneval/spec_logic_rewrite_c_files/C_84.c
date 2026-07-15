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
               (digit_sum_z_84: Z -> Z)
               (binary_output_z_84: Z -> list Z)
               (binary_length_z_84: Z -> Z)
               (digit_sum_state_z_84: Z -> Z -> Z -> Prop)
               (binary_count_state_z_84: Z -> Z -> Z -> Prop)
               (binary_backfill_state_z_84: Z -> Z -> Z -> list Z -> Prop)
               (binary_safe_84: Z -> Prop)
               (solve_safe_84: Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_84 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* to_binary_string(int num)
/*@ Require
        0 <= num && num <= 36 &&
        binary_safe_84(num) &&
        binary_length_z_84(num) + 1 < INT_MAX
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        len == binary_length_z_84(num@pre) &&
        out_l == binary_output_z_84(num@pre) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int bits = 0;
    int x = num;
    char* out = 0;

    if (x == 0) {
        out = malloc_char_array(2);
        out[0] = 48;
        out[1] = 0;
        return out;
    }

    /*@ Inv Assert
        num == num@pre &&
        0 < num && num <= 36 &&
        0 <= x &&
        0 <= bits &&
        out == 0 &&
        binary_safe_84(num@pre) &&
        binary_count_state_z_84(num@pre, x, bits)
    */
    while (x > 0) {
        bits = bits + 1;
        x = x / 2;
    }

    /*@ Assert
        num == num@pre &&
        0 < num && num <= 36 &&
        x == 0 &&
        bits == binary_length_z_84(num@pre) &&
        1 <= bits &&
        out == 0 &&
        binary_safe_84(num@pre) &&
        binary_length_z_84(num@pre) + 1 < INT_MAX
    */

    out = malloc_char_array(bits + 1);
    out[bits] = 0;

    /*@ Assert
        num == num@pre &&
        0 < num && num <= 36 &&
        x == 0 &&
        bits == binary_length_z_84(num@pre) &&
        1 <= bits &&
        out != 0 &&
        binary_safe_84(num@pre) &&
        binary_backfill_state_z_84(num@pre, num, bits, cons(0, nil)) &&
        CharArray::undef_seg(out, 0, bits) *
        CharArray::seg(out, bits, bits + 1, cons(0, nil))
    */

    /*@ Inv Assert exists suffix,
        0 <= num && num <= num@pre &&
        0 < num@pre && num@pre <= 36 &&
        x == 0 &&
        0 <= bits && bits <= binary_length_z_84(num@pre) &&
        out != 0 &&
        binary_safe_84(num@pre) &&
        binary_backfill_state_z_84(num@pre, num, bits, suffix) &&
        Zlength(suffix) == binary_length_z_84(num@pre) + 1 - bits &&
        CharArray::undef_seg(out, 0, bits) *
        CharArray::seg(out, bits, binary_length_z_84(num@pre) + 1, suffix)
    */
    while (num > 0) {
        /*@ Assert exists suffix,
            0 < num && num <= num@pre &&
            0 < num@pre && num@pre <= 36 &&
            x == 0 &&
            0 < bits && bits <= binary_length_z_84(num@pre) &&
            out != 0 &&
            binary_safe_84(num@pre) &&
            binary_backfill_state_z_84(num@pre, num, bits, suffix) &&
            Zlength(suffix) == binary_length_z_84(num@pre) + 1 - bits &&
            CharArray::undef_seg(out, 0, bits) *
            CharArray::seg(out, bits, binary_length_z_84(num@pre) + 1, suffix)
        */
        out[bits - 1] = 48 + (num % 2);
        /*@ Assert exists suffix,
            0 < num && num <= num@pre &&
            0 < num@pre && num@pre <= 36 &&
            x == 0 &&
            0 < bits && bits <= binary_length_z_84(num@pre) &&
            out != 0 &&
            binary_safe_84(num@pre) &&
            binary_backfill_state_z_84(
                num@pre, num / 2, bits - 1, cons(48 + num % 2, suffix)) &&
            Zlength(cons(48 + num % 2, suffix)) ==
                binary_length_z_84(num@pre) + 1 - (bits - 1) &&
            CharArray::undef_seg(out, 0, bits - 1) *
            CharArray::seg(out, bits - 1,
                binary_length_z_84(num@pre) + 1, cons(48 + num % 2, suffix))
        */
        bits = bits - 1;
        num = num / 2;
    }

    /*@ Assert exists suffix,
        num == 0 &&
        num@pre > 0 && num@pre <= 36 &&
        x == 0 &&
        bits == 0 &&
        out != 0 &&
        binary_safe_84(num@pre) &&
        suffix == app(binary_output_z_84(num@pre), cons(0, nil)) &&
        Zlength(suffix) == binary_length_z_84(num@pre) + 1 &&
        CharArray::seg(out, 0, binary_length_z_84(num@pre) + 1, suffix)
    */

    return out;
}

char* solve(int N)
/*@ Require
        0 <= N && N <= 10000 &&
        problem_84_pre_z(N) &&
        solve_safe_84(N)
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        problem_84_spec_z(N@pre, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int sum = 0;

    /*@ Inv Assert
        0 <= N && N <= N@pre &&
        0 <= N@pre && N@pre <= 10000 &&
        0 <= sum && sum <= 36 &&
        problem_84_pre_z(N@pre) &&
        solve_safe_84(N@pre) &&
        digit_sum_state_z_84(N@pre, N, sum)
    */
    while (N > 0) {
        sum = sum + (N % 10);
        N = N / 10;
    }

    /*@ Assert
        N == 0 &&
        0 <= N@pre && N@pre <= 10000 &&
        0 <= sum && sum <= 36 &&
        problem_84_pre_z(N@pre) &&
        solve_safe_84(N@pre) &&
        sum == digit_sum_z_84(N@pre) &&
        binary_safe_84(sum)
    */

    char *result = to_binary_string(sum);

    return result;
}
