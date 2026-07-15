/*
Circular shift the decimal representation of x. If shift is greater than the
number of digits, return the reversed digits.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_65_pre_z: Z -> Z -> Prop)
               (problem_65_spec_z: Z -> Z -> list Z -> Prop)
               (decimal_digits_z_65: Z -> list Z)
               (circular_shift_output_z_65: Z -> Z -> list Z)
               (circular_shift_prefix_z_65: Z -> Z -> Z -> list Z -> Prop)
               (base_count_state_z_65: Z -> Z -> Z -> Z -> Prop)
               (base_fill_full_state_z_65: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_65 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* circular_shift(int x, int shift)
/*@ Require
        0 <= x && x <= INT_MAX &&
        0 <= shift && shift <= INT_MAX &&
        problem_65_pre_z(x, shift) &&
        Zlength(decimal_digits_z_65(x)) + 1 < 64
    Ensure exists out_l len scratch,
        len == Zlength(out_l) &&
        len == Zlength(circular_shift_output_z_65(x, shift)) &&
        problem_65_spec_z(x, shift, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil))) *
        CharArray::full(scratch,
            Zlength(decimal_digits_z_65(x)) + 1,
            app(decimal_digits_z_65(x), cons(0, nil))) *
        CharArray::undef_seg(scratch, Zlength(decimal_digits_z_65(x)) + 1, 64)
*/
{
    char *buf = malloc_char_array(64);
    int n = 0;
    int tmp = 0;
    int i = 0;
    int fill = 0;

    if (x == 0) {
        buf[0] = 48;
        buf[1] = 0;
        n = 1;
        /*@ Assert
            x == x@pre &&
            shift == shift@pre &&
            x == 0 &&
            0 <= x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            tmp == 0 &&
            i == 0 &&
            fill == 0 &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64)
        */
    } else {
        tmp = x;
        /*@ Inv Assert
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            0 <= tmp &&
            0 <= n && n < 64 &&
            i == 0 &&
            fill == 0 &&
            base_count_state_z_65(x, 10, tmp, n) &&
            CharArray::undef_full(buf, 64)
        */
        while (tmp > 0) {
            n = n + 1;
            tmp = tmp / 10;
        }

        /*@ Assert
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            tmp == 0 &&
            i == 0 &&
            fill == 0 &&
            CharArray::undef_full(buf, 64)
        */

        /*@ Inv Assert
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            tmp == 0 &&
            fill == 0 &&
            0 <= i && i <= n + 1 &&
            CharArray::full(buf, i, repeat_Z(0, i)) *
            CharArray::undef_seg(buf, i, 64)
        */
        for (i = 0; i <= n; i++) {
            buf[i] = 0;
        }

        /*@ Assert exists out_l,
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            tmp == 0 &&
            i == n + 1 &&
            fill == 0 &&
            Zlength(out_l) == n &&
            base_fill_full_state_z_65(x, 10, x, n, out_l) &&
            CharArray::full(buf, n + 1, app(out_l, cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64)
        */

        tmp = x;
        fill = n;

        /*@ Inv Assert exists out_l,
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            i == n + 1 &&
            0 <= tmp &&
            0 <= fill && fill <= n &&
            Zlength(out_l) == n &&
            base_fill_full_state_z_65(x, 10, tmp, fill, out_l) &&
            CharArray::full(buf, n + 1, app(out_l, cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64)
        */
        while (tmp > 0) {
            fill = fill - 1;
            /*@ Assert exists out_l,
                x == x@pre &&
                shift == shift@pre &&
                0 < x && x <= INT_MAX &&
                0 <= shift && shift <= INT_MAX &&
                n == Zlength(decimal_digits_z_65(x)) &&
                Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
                problem_65_pre_z(x, shift) &&
                i == n + 1 &&
                0 < tmp &&
                0 <= fill && fill < n &&
                Zlength(out_l) == n &&
                base_fill_full_state_z_65(x, 10, tmp, fill + 1, out_l) &&
                CharArray::full(buf, n + 1, app(out_l, cons(0, nil))) *
                CharArray::undef_seg(buf, n + 1, 64)
            */
            buf[fill] = 48 + (tmp % 10);
            tmp = tmp / 10;
        }

        /*@ Assert exists out_l,
            x == x@pre &&
            shift == shift@pre &&
            0 < x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            problem_65_pre_z(x, shift) &&
            tmp == 0 &&
            fill == 0 &&
            i == n + 1 &&
            out_l == decimal_digits_z_65(x) &&
            Zlength(out_l) == n &&
            CharArray::full(buf, n + 1, app(out_l, cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64)
        */
    }

    /*@ Assert
        x == x@pre &&
        shift == shift@pre &&
        0 <= x && x <= INT_MAX &&
        0 <= shift && shift <= INT_MAX &&
        0 <= tmp &&
        0 <= i &&
        0 <= fill &&
        n == Zlength(decimal_digits_z_65(x)) &&
        Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
        problem_65_pre_z(x, shift) &&
        CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
        CharArray::undef_seg(buf, n + 1, 64)
    */

    char *out = malloc_char_array(n + 1);

    if (n < shift) {
        /*@ Inv Assert exists out_l,
            x == x@pre &&
            shift == shift@pre &&
            0 <= x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            0 <= tmp &&
            0 <= i &&
            0 <= fill &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            n < shift &&
            0 <= i && i <= n &&
            circular_shift_prefix_z_65(x, shift, i, out_l) &&
            Zlength(out_l) == i &&
            problem_65_pre_z(x, shift) &&
            CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64) *
            CharArray::full(out, i, out_l) *
            CharArray::undef_seg(out, i, n + 1)
        */
        for (i = 0; i < n; i++) {
            out[i] = buf[n - 1 - i];
        }
    } else {
        /*@ Inv Assert exists out_l,
            x == x@pre &&
            shift == shift@pre &&
            0 <= x && x <= INT_MAX &&
            0 <= shift && shift <= INT_MAX &&
            0 <= tmp &&
            0 <= fill &&
            n == Zlength(decimal_digits_z_65(x)) &&
            Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
            n >= shift &&
            0 <= i && i <= n &&
            circular_shift_prefix_z_65(x, shift, i, out_l) &&
            Zlength(out_l) == i &&
            problem_65_pre_z(x, shift) &&
            CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
            CharArray::undef_seg(buf, n + 1, 64) *
            CharArray::full(out, i, out_l) *
            CharArray::undef_seg(out, i, n + 1)
        */
        for (i = 0; i < n; i++) {
            int src = n - shift + i;
            if (src >= n) {
                src = src - n;
            }
            /*@ Assert exists out_l,
                x == x@pre &&
                shift == shift@pre &&
                0 <= x && x <= INT_MAX &&
                0 <= shift && shift <= INT_MAX &&
                0 <= tmp &&
                0 <= fill &&
                n == Zlength(decimal_digits_z_65(x)) &&
                Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
                n >= shift &&
                0 <= i && i < n &&
                0 <= src && src < n &&
                src == (n - shift + i) % n &&
                circular_shift_prefix_z_65(x, shift, i, out_l) &&
                Zlength(out_l) == i &&
                problem_65_pre_z(x, shift) &&
                CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
                CharArray::undef_seg(buf, n + 1, 64) *
                CharArray::full(out, i, out_l) *
                CharArray::undef_seg(out, i, n + 1)
            */
            out[i] = buf[src];
        }
    }

    /*@ Assert exists out_l,
        x == x@pre &&
        shift == shift@pre &&
        0 <= x && x <= INT_MAX &&
        0 <= shift && shift <= INT_MAX &&
        0 <= tmp &&
        0 <= fill &&
        i == n &&
        n == Zlength(decimal_digits_z_65(x)) &&
        Zlength(decimal_digits_z_65(x)) + 1 < 64 &&
        circular_shift_prefix_z_65(x, shift, n, out_l) &&
        out_l == circular_shift_output_z_65(x, shift) &&
        Zlength(out_l) == n &&
        problem_65_pre_z(x, shift) &&
        CharArray::full(buf, n + 1, app(decimal_digits_z_65(x), cons(0, nil))) *
        CharArray::undef_seg(buf, n + 1, 64) *
        CharArray::full(out, n, out_l) *
        CharArray::undef_seg(out, n, n + 1)
    */

    out[n] = 0;
    return out;
}
