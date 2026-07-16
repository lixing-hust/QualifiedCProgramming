/*
You are given two positive integers n && m, && your task is to compute the
average of the integers from n through m (including n && m).
Round the answer to the nearest integer(smaller one) && convert that to binary.
If n is greater than m, return "-1".
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010"
*/
#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_103_pre_z: Z -> Z -> Prop)
               (problem_103_spec_z: Z -> Z -> list Z -> Prop)
               (binary_output_z_103: Z -> list Z)
               (binary_length_z_103: Z -> Z)
               (binary_count_state_z_103: Z -> Z -> Z -> Prop)
               (binary_backfill_state_z_103: Z -> Z -> Z -> list Z -> Prop)
               (binary_safe_103: Z -> Prop)
               (rounded_avg_safe_103: Z -> Z -> Prop)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_103 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* to_binary_string(int num)
/*@ Require
        0 <= num && num <= INT_MAX &&
        binary_safe_103(num)
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        len == binary_length_z_103(num@pre) &&
        out_l == binary_output_z_103(num@pre) &&
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
        0 < num && num <= INT_MAX &&
        0 <= x &&
        0 <= bits &&
        out == 0 &&
        binary_safe_103(num@pre) &&
        binary_count_state_z_103(num@pre, x, bits)
    */
    while (x > 0) {
        bits = bits + 1;
        x = x / 2;
    }

    /*@ Assert
        num == num@pre &&
        0 < num && num <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_103(num@pre) &&
        1 <= bits &&
        out == 0 &&
        binary_safe_103(num@pre)
    */

    out = malloc_char_array(bits + 1);
    out[bits] = 0;

    /*@ Assert
        num == num@pre &&
        0 < num && num <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_103(num@pre) &&
        1 <= bits &&
        out != 0 &&
        binary_safe_103(num@pre) &&
        binary_backfill_state_z_103(num@pre, num, bits, cons(0, nil)) &&
        CharArray::undef_seg(out, 0, bits) *
        CharArray::seg(out, bits, bits + 1, cons(0, nil))
    */

    /*@ Inv Assert exists suffix,
        0 <= num && num <= num@pre &&
        0 < num@pre && num@pre <= INT_MAX &&
        x == 0 &&
        0 <= bits && bits <= binary_length_z_103(num@pre) &&
        out != 0 &&
        binary_safe_103(num@pre) &&
        binary_backfill_state_z_103(num@pre, num, bits, suffix) &&
        Zlength(suffix) == binary_length_z_103(num@pre) + 1 - bits &&
        CharArray::undef_seg(out, 0, bits) *
        CharArray::seg(out, bits, binary_length_z_103(num@pre) + 1, suffix)
    */
    while (num > 0) {
        /*@ Assert exists suffix,
            0 < num && num <= num@pre &&
            0 < num@pre && num@pre <= INT_MAX &&
            x == 0 &&
            0 < bits && bits <= binary_length_z_103(num@pre) &&
            out != 0 &&
            binary_safe_103(num@pre) &&
            binary_backfill_state_z_103(num@pre, num, bits, suffix) &&
            Zlength(suffix) == binary_length_z_103(num@pre) + 1 - bits &&
            CharArray::undef_seg(out, 0, bits) *
            CharArray::seg(out, bits, binary_length_z_103(num@pre) + 1, suffix)
        */
        out[bits - 1] = 48 + (num % 2);
        /*@ Assert exists suffix,
            0 < num && num <= num@pre &&
            0 < num@pre && num@pre <= INT_MAX &&
            x == 0 &&
            0 < bits && bits <= binary_length_z_103(num@pre) &&
            out != 0 &&
            binary_safe_103(num@pre) &&
            binary_backfill_state_z_103(
                num@pre, num / 2, bits - 1,
                cons(48 + num % 2, suffix)) &&
            Zlength(cons(48 + num % 2, suffix)) ==
                binary_length_z_103(num@pre) + 1 - (bits - 1) &&
            CharArray::undef_seg(out, 0, bits - 1) *
            CharArray::seg(out, bits - 1,
                binary_length_z_103(num@pre) + 1,
                cons(48 + num % 2, suffix))
        */
        bits = bits - 1;
        num = num / 2;
    }

    /*@ Assert exists suffix,
        num == 0 &&
        0 < num@pre && num@pre <= INT_MAX &&
        x == 0 &&
        bits == 0 &&
        out != 0 &&
        binary_safe_103(num@pre) &&
        suffix == app(binary_output_z_103(num@pre), cons(0, nil)) &&
        Zlength(suffix) == binary_length_z_103(num@pre) + 1 &&
        CharArray::seg(out, 0, binary_length_z_103(num@pre) + 1, suffix)
    */

    return out;
}

char* rounded_avg(int n, int m)
/*@ Require
        0 < n && n <= INT_MAX &&
        0 < m && m <= INT_MAX &&
        n + m <= INT_MAX &&
        problem_103_pre_z(n, m) &&
        rounded_avg_safe_103(n, m)
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        problem_103_spec_z(n@pre, m@pre, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int num;
    char* out;
    if (n > m) {
        out = malloc_char_array(3);
        out[0] = 45;
        out[1] = 49;
        out[2] = 0;
        return out;
    }
    num = (m + n) / 2;
    return to_binary_string(num);
}
