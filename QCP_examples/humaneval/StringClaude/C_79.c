/*
You will be given a number in decimal form && your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' || '1'.

There will be an extra couple of characters "db" at the beginning && at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15)   // returns "db1111db"
decimal_to_binary(32)   // returns "db100000db"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_79_pre_z: Z -> Prop)
               (problem_79_spec_z: Z -> list Z -> Prop)
               (binary_digits_z: Z -> list Z)
               (binary_count_state_z: Z -> Z -> Z -> Prop)
               (decimal_binary_full_state_z: Z -> Z -> Z -> list Z -> Prop)
               (decorated_binary_digits_z: Z -> list Z)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import coins_79 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* decimal_to_binary(int decimal)
/*@ Require
        0 <= decimal && decimal + 5 < INT_MAX &&
        problem_79_pre_z(decimal)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_79_spec_z(decimal, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (decimal == 0) {
        char *out_zero = malloc_char_array(6);
        out_zero[0] = 100;
        out_zero[1] = 98;
        out_zero[2] = 48;
        out_zero[3] = 100;
        out_zero[4] = 98;
        out_zero[5] = 0;
        return out_zero;
    } else {
        int orig = decimal;
        int x = decimal;
        int bits = 0;
        int total = 0;
        int i = 0;
        int num = decimal;
        char *out = 0;

        /*@ Inv Assert
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            total == 0 &&
            i == 0 &&
            out == 0 &&
            0 <= x &&
            0 <= bits && bits < INT_MAX &&
            binary_count_state_z(decimal, x, bits)
        */
        while (x > 0) {
            bits = bits + 1;
            x = x / 2;
        }

        total = bits;
        out = malloc_char_array(total + 5);

        out[0] = 100;
        out[1] = 98;
        i = 0;

        /*@ Inv Assert
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            x == 0 &&
            total == Zlength(binary_digits_z(decimal)) &&
            bits == total &&
            0 <= i && i <= total &&
            CharArray::seg(out, 2, i + 2, repeat_Z(0, i)) *
            CharArray::undef_seg(out, i + 2, total + 5) *
            CharArray::full(out, 2, cons(100, cons(98, nil)))
        */
        while (i < total) {
            out[i + 2] = 0;
            i = i + 1;
        }

        /*@ Assert
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            x == 0 &&
            total == Zlength(binary_digits_z(decimal)) &&
            bits == total &&
            i == total &&
            CharArray::seg(out, 2, total + 2, repeat_Z(0, total)) *
            CharArray::undef_seg(out, total + 2, total + 4) *
            CharArray::undef_seg(out, total + 4, total + 5) *
            CharArray::full(out, 2, cons(100, cons(98, nil)))
        */
        out[total + 4] = 0;

        /*@ Assert
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            x == 0 &&
            total == Zlength(binary_digits_z(decimal)) &&
            bits == total &&
            i == total &&
            CharArray::seg(out, 2, total + 2, repeat_Z(0, total)) *
            CharArray::undef_seg(out, total + 2, total + 3) *
            CharArray::undef_seg(out, total + 3, total + 4) *
            CharArray::seg(out, total + 4, total + 5, cons(0, nil)) *
            CharArray::full(out, 2, cons(100, cons(98, nil)))
        */
        out[total + 3] = 98;

        /*@ Assert
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            x == 0 &&
            total == Zlength(binary_digits_z(decimal)) &&
            bits == total &&
            i == total &&
            CharArray::seg(out, 2, total + 2, repeat_Z(0, total)) *
            CharArray::undef_seg(out, total + 2, total + 3) *
            CharArray::seg(out, total + 3, total + 5, cons(98, cons(0, nil))) *
            CharArray::full(out, 2, cons(100, cons(98, nil)))
        */
        out[total + 2] = 100;

        /*@ Assert
            exists out_l,
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            num == decimal &&
            x == 0 &&
            i == total &&
            total == Zlength(binary_digits_z(decimal)) &&
            bits == total &&
            Zlength(out_l) == total + 4 &&
            decimal_binary_full_state_z(decimal, decimal, bits, out_l) &&
            CharArray::full(out, total + 5, app(out_l, cons(0, nil)))
        */

        i = total + 5;

        /*@ Inv Assert
            exists out_l,
            decimal == decimal@pre &&
            0 < decimal && decimal + 5 < INT_MAX &&
            orig == decimal &&
            x == 0 &&
            i == total + 5 &&
            total == Zlength(binary_digits_z(orig)) &&
            0 <= bits && bits <= total &&
            0 <= num &&
            Zlength(out_l) == total + 4 &&
            decimal_binary_full_state_z(orig, num, bits, out_l) &&
            CharArray::full(out, total + 5, app(out_l, cons(0, nil)))
        */
        while (num > 0) {
            bits = bits - 1;
            /*@ Assert
                exists out_l,
                decimal == decimal@pre &&
                0 < decimal && decimal + 5 < INT_MAX &&
                orig == decimal &&
                x == 0 &&
                0 < num &&
                i == total + 5 &&
                total == Zlength(binary_digits_z(orig)) &&
                0 <= bits && bits < total &&
                Zlength(out_l) == total + 4 &&
                decimal_binary_full_state_z(orig, num, bits + 1, out_l) &&
                CharArray::full(out, total + 5, app(out_l, cons(0, nil)))
            */
            out[bits + 2] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
