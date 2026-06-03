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
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_103_pre_z: Z -> Z -> Prop)
               (problem_103_spec_z: Z -> Z -> list Z -> Prop)
               (avg_103: Z -> Z -> Z)
               (binary_digits_z: Z -> list Z)
               (binary_count_state_z: Z -> Z -> Z -> Prop)
               (binary_fill_full_state_z: Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_103 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* rounded_avg(int n, int m)
/*@ Require
        0 < n && 0 < m &&
        n < INT_MAX && m < INT_MAX &&
        n + m < INT_MAX &&
        problem_103_pre_z(n, m)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_103_spec_z(n, m, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (n > m) {
        char *out_neg = malloc_char_array(3);
        out_neg[0] = 45;
        out_neg[1] = 49;
        out_neg[2] = 0;
        return out_neg;
    } else {
        int num = (n + m) / 2;
        int orig = num;
        int digits = 0;
        int t = num;
        int total = 0;
        int i = 0;
        char *out = 0;

        /*@ Inv Assert
            n == n@pre &&
            m == m@pre &&
            0 < n && 0 < m &&
            n <= m &&
            n + m < INT_MAX &&
            num == avg_103(n, m) &&
            orig == num &&
            0 < num && num < INT_MAX &&
            0 <= t &&
            0 <= digits && digits < INT_MAX &&
            total == 0 &&
            i == 0 &&
            out == 0 &&
            binary_count_state_z(num, t, digits)
        */
        while (t > 0) {
            digits = digits + 1;
            t = t / 2;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        /*@ Inv Assert
            n == n@pre &&
            m == m@pre &&
            0 < n && 0 < m &&
            n <= m &&
            n + m < INT_MAX &&
            num == avg_103(n, m) &&
            orig == num &&
            0 < num && num < INT_MAX &&
            t == 0 &&
            total == Zlength(binary_digits_z(num)) &&
            digits == total &&
            0 <= i && i <= total + 1 &&
            CharArray::full(out, i, repeat_Z(0, i)) *
            CharArray::undef_seg(out, i, total + 1)
        */
        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }

        /*@ Assert
            exists out_l,
            n == n@pre &&
            m == m@pre &&
            0 < n && 0 < m &&
            n <= m &&
            n + m < INT_MAX &&
            num == avg_103(n, m) &&
            orig == num &&
            0 < num && num < INT_MAX &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(binary_digits_z(num)) &&
            digits == total &&
            Zlength(out_l) == total &&
            binary_fill_full_state_z(num, num, digits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */

        /*@ Inv Assert
            exists out_l,
            n == n@pre &&
            m == m@pre &&
            0 < n && 0 < m &&
            n <= m &&
            n + m < INT_MAX &&
            orig == avg_103(n, m) &&
            0 < orig && orig < INT_MAX &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(binary_digits_z(orig)) &&
            0 <= digits && digits <= total &&
            0 <= num &&
            Zlength(out_l) == total &&
            binary_fill_full_state_z(orig, num, digits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */
        while (num > 0) {
            digits = digits - 1;
            /*@ Assert
                exists out_l,
                n == n@pre &&
                m == m@pre &&
                0 < n && 0 < m &&
                n <= m &&
                n + m < INT_MAX &&
                orig == avg_103(n, m) &&
                0 < orig && orig < INT_MAX &&
                0 < num &&
                t == 0 &&
                i == total + 1 &&
                total == Zlength(binary_digits_z(orig)) &&
                0 <= digits && digits < total &&
                Zlength(out_l) == total &&
                binary_fill_full_state_z(orig, num, digits + 1, out_l) &&
                CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
            */
            out[digits] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
