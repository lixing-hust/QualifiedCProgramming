/*
Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
"0"
>>> string_sequence(5)
"0 1 2 3 4 5"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_15_pre_z: Z -> Prop)
               (problem_15_spec_z: Z -> list Z -> Prop)
               (sequence_prefix_z: Z -> list Z)
               (sequence_output_z: Z -> list Z)
               (sequence_output_bound_z: Z -> Prop)
               (base_digits_z: Z -> Z -> list Z)
               (base_count_state_z: Z -> Z -> Z -> Z -> Prop)
               (base_fill_full_state_z: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_44 */
/*@ Import Coq Require Import coins_15 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* string_sequence(int n)
/*@ Require
        0 <= n &&
        12 * (n + 1) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        sequence_output_bound_z(n)
    Ensure exists out_l len cap,
        cap == 12 * (n + 1) + 1 &&
        len == Zlength(out_l) &&
        problem_15_spec_z(n, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_seg(__return, len + 1, cap)
*/
{
    int cap = 12 * (n + 1) + 1;
    char *out = malloc_char_array(cap);
    int k = 0;
    int i = 1;

    out[0] = 48;
    k = 1;

    {
    int t = 0;
    int digits = 0;
    int j = 0;
    int fill = 0;

    /*@ Inv Assert
        exists out_l,
        n == n@pre &&
        cap == 12 * (n + 1) + 1 &&
        out != 0 &&
        0 <= n &&
        12 * (n + 1) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        sequence_output_bound_z(n) &&
        1 <= i && i <= n + 1 &&
        k == Zlength(out_l) &&
        out_l == sequence_prefix_z(i) &&
        k + 1 <= cap &&
        0 <= t &&
        0 <= digits &&
        0 <= j &&
        fill == 0 &&
        CharArray::full(out, k, out_l) *
        CharArray::undef_seg(out, k, cap)
    */
    for (i = 1; i <= n; i++) {
        t = i;
        digits = 0;

        /*@ Inv Assert
            exists out_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            k == Zlength(out_l) &&
            out_l == sequence_prefix_z(i) &&
            k + 1 <= cap &&
            0 <= t &&
            0 <= digits &&
            0 <= j &&
            fill == 0 &&
            base_count_state_z(i, 10, t, digits) &&
            CharArray::full(out, k, out_l) *
            CharArray::undef_seg(out, k, cap)
        */
        while (t > 0) {
            digits = digits + 1;
            t = t / 10;
        }

        /*@ Assert
            exists out_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            k == Zlength(out_l) &&
            out_l == sequence_prefix_z(i) &&
            digits == Zlength(base_digits_z(i, 10)) &&
            k + 1 + digits < cap &&
            t == 0 &&
            0 <= digits &&
            0 <= j &&
            fill == 0 &&
            CharArray::full(out, k, out_l) *
            CharArray::undef_seg(out, k, cap)
        */

        out[k] = 32;
        k = k + 1;

        /*@ Inv Assert
            exists prefix_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            prefix_l == sequence_prefix_z(i) &&
            k == Zlength(prefix_l) + 1 &&
            digits == Zlength(base_digits_z(i, 10)) &&
            k + digits < cap &&
            t == 0 &&
            0 <= digits &&
            0 <= j && j <= digits &&
            fill == 0 &&
            CharArray::full(out, k + j, app(app(prefix_l, cons(32, nil)), repeat_Z(0, j))) *
            CharArray::undef_seg(out, k + j, cap)
        */
        for (j = 0; j < digits; j++) {
            out[k + j] = 0;
        }

        /*@ Assert
            exists prefix_l digit_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            prefix_l == sequence_prefix_z(i) &&
            k == Zlength(prefix_l) + 1 &&
            digits == Zlength(base_digits_z(i, 10)) &&
            j == digits &&
            t == 0 &&
            0 <= digits &&
            fill == 0 &&
            Zlength(digit_l) == digits &&
            base_fill_full_state_z(i, 10, i, digits, digit_l) &&
            CharArray::full(out, k + digits, app(app(prefix_l, cons(32, nil)), digit_l)) *
            CharArray::undef_seg(out, k + digits, cap)
        */

        t = i;
        fill = digits;

        /*@ Inv Assert
            exists prefix_l digit_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            prefix_l == sequence_prefix_z(i) &&
            k == Zlength(prefix_l) + 1 &&
            digits == Zlength(base_digits_z(i, 10)) &&
            0 <= k &&
            j == digits &&
            0 <= t &&
            0 <= fill && fill <= digits &&
            k + digits < cap &&
            Zlength(digit_l) == digits &&
            base_fill_full_state_z(i, 10, t, fill, digit_l) &&
            CharArray::full(out, k + digits, app(app(prefix_l, cons(32, nil)), digit_l)) *
            CharArray::undef_seg(out, k + digits, cap)
        */
        while (t > 0) {
            fill = fill - 1;
            /*@ Assert
                exists prefix_l digit_l,
                n == n@pre &&
                cap == 12 * (n + 1) + 1 &&
                out != 0 &&
                0 <= n &&
                12 * (n + 1) + 1 < INT_MAX &&
                problem_15_pre_z(n) &&
                sequence_output_bound_z(n) &&
                1 <= i && i <= n &&
                prefix_l == sequence_prefix_z(i) &&
                k == Zlength(prefix_l) + 1 &&
                digits == Zlength(base_digits_z(i, 10)) &&
                0 <= k &&
                j == digits &&
                0 < t &&
                0 <= fill && fill < digits &&
                0 <= k + fill && k + fill < k + digits &&
                k + digits < cap &&
                0 <= 48 + t % 10 && 48 + t % 10 <= 127 &&
                Zlength(digit_l) == digits &&
                base_fill_full_state_z(i, 10, t, fill + 1, digit_l) &&
                CharArray::full(out, k + digits, app(app(prefix_l, cons(32, nil)), digit_l)) *
                CharArray::undef_seg(out, k + digits, cap)
            */
            out[k + fill] = 48 + (t % 10);
            t = t / 10;
        }

        /*@ Assert
            exists out_l,
            n == n@pre &&
            cap == 12 * (n + 1) + 1 &&
            out != 0 &&
            0 <= n &&
            12 * (n + 1) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            sequence_output_bound_z(n) &&
            1 <= i && i <= n &&
            out_l == sequence_prefix_z(i + 1) &&
            k + digits == Zlength(out_l) &&
            k + digits < cap &&
            t == 0 &&
            fill == 0 &&
            j == digits &&
            digits == Zlength(base_digits_z(i, 10)) &&
            CharArray::full(out, k + digits, out_l) *
            CharArray::undef_seg(out, k + digits, cap)
        */
        k = k + digits;
    }
    }

    out[k] = 0;
    /*@ Assert
        exists out_l len,
        n == n@pre &&
        cap == 12 * (n + 1) + 1 &&
        out != 0 &&
        len == Zlength(out_l) &&
        out_l == sequence_output_z(n) &&
        k == len &&
        i == n + 1 &&
        0 <= n &&
        12 * (n + 1) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        sequence_output_bound_z(n) &&
        problem_15_spec_z(n, out_l) &&
        CharArray::full(out, len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_seg(out, len + 1, cap)
    */
    return out;
}
