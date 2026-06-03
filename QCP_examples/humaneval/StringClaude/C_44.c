/*
Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> change_base(8, 3)
"22"
>>> change_base(8, 2)
"1000"
>>> change_base(7, 2)
"111"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_44_pre_z: Z -> Z -> Prop)
               (problem_44_spec_z: Z -> Z -> list Z -> Prop)
               (base_digits_z: Z -> Z -> list Z)
               (base_digits_pos_z: Z -> Z -> list Z)
               (base_count_state_z: Z -> Z -> Z -> Z -> Prop)
               (base_fill_state_z: Z -> Z -> Z -> Z -> list Z -> Prop)
               (base_fill_full_state_z: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_44 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* change_base(int x, int base)
/*@ Require
        0 <= x && x < INT_MAX &&
        2 <= base && base < 10 &&
        problem_44_pre_z(x, base)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_44_spec_z(x, base, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (x == 0) {
        char *out0 = malloc_char_array(2);
        out0[0] = 48;
        out0[1] = 0;
        return out0;
    } else {
        int digits = 0;
        int t = x;
        int total = 0;
        char *out = 0;
        int i = 0;

        /*@ Inv Assert
            x == x@pre &&
            base == base@pre &&
            0 < x && x < INT_MAX &&
            2 <= base && base < 10 &&
            0 <= t &&
            0 <= digits && digits < INT_MAX &&
            total == 0 &&
            out == 0 &&
            i == 0 &&
            base_count_state_z(x, base, t, digits)
        */
        while (t > 0) {
            digits = digits + 1;
            t = t / base;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        /*@ Inv Assert
            x@pre > 0 &&
            x@pre < INT_MAX &&
            base == base@pre &&
            2 <= base && base < 10 &&
            t == 0 &&
            total == Zlength(base_digits_z(x@pre, base)) &&
            digits == total &&
            x == x@pre &&
            0 <= i && i <= total + 1 &&
            CharArray::full(out, i, repeat_Z(0, i)) *
            CharArray::undef_seg(out, i, total + 1)
        */
        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }

        /*@ Assert
            exists out_l,
            x@pre > 0 &&
            x@pre < INT_MAX &&
            base == base@pre &&
            2 <= base && base < 10 &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(base_digits_z(x@pre, base)) &&
            digits == total &&
            x == x@pre &&
            Zlength(out_l) == total &&
            base_fill_full_state_z(x@pre, base, x, digits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */

        /*@ Inv Assert
            exists out_l,
            x@pre > 0 &&
            x@pre < INT_MAX &&
            base == base@pre &&
            2 <= base && base < 10 &&
            t == 0 &&
            i == total + 1 &&
            total == Zlength(base_digits_z(x@pre, base)) &&
            0 <= digits && digits <= total &&
            0 <= x &&
            Zlength(out_l) == total &&
            base_fill_full_state_z(x@pre, base, x, digits, out_l) &&
            CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
        */
        while (x > 0) {
            digits = digits - 1;
            /*@ Assert
                exists out_l,
                x@pre > 0 &&
                x@pre < INT_MAX &&
                base == base@pre &&
                2 <= base && base < 10 &&
                t == 0 &&
                i == total + 1 &&
                total == Zlength(base_digits_z(x@pre, base)) &&
                0 <= digits && digits < total &&
                0 < x &&
                Zlength(out_l) == total &&
                base_fill_full_state_z(x@pre, base, x, digits + 1, out_l) &&
                CharArray::full(out, total + 1, app(out_l, cons(0, nil)))
            */
            out[digits] = 48 + (x % base);
            x = x / base;
        }
        return out;
    }
}
