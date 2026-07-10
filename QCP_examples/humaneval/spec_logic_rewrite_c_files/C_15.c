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
               (decimal_digits_z: Z -> list Z)
               (decimal_count_state_z: Z -> Z -> Z -> Prop)
               (decimal_fill_full_state_z: Z -> Z -> Z -> list Z -> Prop)
               (string_sequence_prefix_z: Z -> list Z)
               (sequence_len_z: Z -> Z)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_15 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int decimal_len(int value)
/*@ Require
        0 <= value && value < INT_MAX
    Ensure
        __return == Zlength(decimal_digits_z(value)) &&
        1 <= __return && __return < INT_MAX
*/
{
    if (value == 0) {
        return 1;
    } else {
        int tmp = value;
        int digits = 0;
        /*@ Inv Assert
            value == value@pre &&
            0 < value && value < INT_MAX &&
            0 <= tmp &&
            0 <= digits && digits < INT_MAX &&
            decimal_count_state_z(value, tmp, digits)
        */
        while (tmp > 0) {
            digits = digits + 1;
            tmp = tmp / 10;
        }
        return digits;
    }
}

void write_decimal(char *buf, int value, int digits)
/*@ Require
        0 <= value && value < INT_MAX &&
        digits == Zlength(decimal_digits_z(value)) &&
        1 <= digits && digits < INT_MAX &&
        CharArray::undef_full(buf, digits)
    Ensure
        CharArray::full(buf, digits, decimal_digits_z(value))
*/
{
    if (value == 0) {
        buf[0] = 48;
    } else {
        int tmp = value;
        int i = 0;
        int fill = digits;
        /*@ Inv Assert
            buf == buf@pre &&
            value == value@pre &&
            digits == digits@pre &&
            0 < value && value < INT_MAX &&
            digits == Zlength(decimal_digits_z(value)) &&
            1 <= digits && digits < INT_MAX &&
            tmp == value &&
            fill == digits &&
            0 <= i && i <= digits &&
            CharArray::full(buf, i, repeat_Z(0, i)) *
            CharArray::undef_seg(buf, i, digits)
        */
        while (i < digits) {
            buf[i] = 0;
            i = i + 1;
        }

        /*@ Assert exists out_l,
            buf == buf@pre &&
            value == value@pre &&
            digits == digits@pre &&
            0 < value && value < INT_MAX &&
            digits == Zlength(decimal_digits_z(value)) &&
            1 <= digits && digits < INT_MAX &&
            tmp == value &&
            fill == digits &&
            i == digits &&
            Zlength(out_l) == digits &&
            decimal_fill_full_state_z(value, tmp, fill, out_l) &&
            CharArray::full(buf, digits, out_l)
        */

        /*@ Inv Assert exists out_l,
            buf == buf@pre &&
            value == value@pre &&
            digits == digits@pre &&
            0 < value && value < INT_MAX &&
            digits == Zlength(decimal_digits_z(value)) &&
            1 <= digits && digits < INT_MAX &&
            i == digits &&
            0 <= tmp &&
            0 <= fill && fill <= digits &&
            Zlength(out_l) == digits &&
            decimal_fill_full_state_z(value, tmp, fill, out_l) &&
            CharArray::full(buf, digits, out_l)
        */
        while (tmp > 0) {
            fill = fill - 1;
            /*@ Assert exists out_l,
                buf == buf@pre &&
                value == value@pre &&
                digits == digits@pre &&
                0 < value && value < INT_MAX &&
                digits == Zlength(decimal_digits_z(value)) &&
                1 <= digits && digits < INT_MAX &&
                i == digits &&
                0 < tmp &&
                0 <= fill && fill < digits &&
                Zlength(out_l) == digits &&
                decimal_fill_full_state_z(value, tmp, fill + 1, out_l) &&
                CharArray::full(buf, digits, out_l)
            */
            buf[fill] = 48 + (tmp % 10);
            tmp = tmp / 10;
        }
    }
}

char* string_sequence(int n)
/*@ Require
        0 <= n && n < INT_MAX &&
        sequence_len_z(n) + 1 < INT_MAX &&
        problem_15_pre_z(n)
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        len == sequence_len_z(n) &&
        problem_15_spec_z(n, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int total = 1;
    int i = 1;
    int k = 0;
    int len = 0;
    char *out = 0;

    /*@ Inv Assert
        n == n@pre &&
        0 <= n && n < INT_MAX &&
        sequence_len_z(n) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        1 <= i && i <= n + 1 &&
        total == Zlength(string_sequence_prefix_z(i)) &&
        total <= sequence_len_z(n) &&
        k == 0 &&
        len >= 0 &&
        out == 0
    */
    while (i <= n) {
        len = decimal_len(i);
        total = total + 1 + len;
        i = i + 1;
    }

    out = malloc_char_array(total + 1);
    /*@ Assert
        n == n@pre &&
        0 <= n && n < INT_MAX &&
        sequence_len_z(n) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        i == n + 1 &&
        total == sequence_len_z(n) &&
        0 <= total &&
        k == 0 &&
        len >= 0 &&
        out != 0 &&
        CharArray::undef_full(out, total + 1)
    */
    out[0] = 48;
    k = 1;
    i = 1;

    /*@ Inv Assert exists out_l,
        n == n@pre &&
        0 <= n && n < INT_MAX &&
        sequence_len_z(n) + 1 < INT_MAX &&
        problem_15_pre_z(n) &&
        total == sequence_len_z(n) &&
        1 <= i && i <= n + 1 &&
        0 <= k && k <= total &&
        k == Zlength(out_l) &&
        out_l == string_sequence_prefix_z(i) &&
        len >= 0 &&
        CharArray::full(out, k, out_l) *
        CharArray::undef_seg(out, k, total + 1)
    */
    while (i <= n) {
        out[k] = 32;
        k = k + 1;
        len = decimal_len(i);
        /*@ Assert exists out_l,
            n == n@pre &&
            0 <= n && n < INT_MAX &&
            sequence_len_z(n) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            total == sequence_len_z(n) &&
            1 <= i && i <= n &&
            len == Zlength(decimal_digits_z(i)) &&
            1 <= len && len < INT_MAX &&
            k == Zlength(out_l) + 1 &&
            out_l == string_sequence_prefix_z(i) &&
            CharArray::full(out, k, app(out_l, cons(32, nil))) *
            CharArray::undef_full(out + k * sizeof(char), len) *
            CharArray::undef_seg(out, k + len, total + 1)
        */
        write_decimal(out + k, i, len);
        k = k + len;
        i = i + 1;
        /*@ Assert exists out_l,
            n == n@pre &&
            0 <= n && n < INT_MAX &&
            sequence_len_z(n) + 1 < INT_MAX &&
            problem_15_pre_z(n) &&
            total == sequence_len_z(n) &&
            1 <= i && i <= n + 1 &&
            k == Zlength(out_l) &&
            out_l == string_sequence_prefix_z(i) &&
            len >= 0 &&
            CharArray::full(out, k, out_l) *
            CharArray::undef_seg(out, k, total + 1)
        */
    }

    out[k] = 0;
    return out;
}
