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
               (binary_safe_79: Z -> Prop)
               (binary_length_z_79: Z -> Z)
               (binary_payload_z_79: Z -> list Z)
               (decorated_binary_output_z_79: Z -> list Z)
               (binary_count_state_z_79: Z -> Z -> Z -> Prop)
               (binary_divisor_state_z_79: Z -> Z -> Z -> Prop)
               (binary_write_state_z_79: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_79 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* decimal_to_binary(int decimal)
/*@ Require
        0 <= decimal && decimal <= INT_MAX &&
        problem_79_pre_z(decimal) &&
        binary_safe_79(decimal) &&
        binary_length_z_79(decimal) + 5 < INT_MAX
    Ensure exists out_l len,
        len == Zlength(out_l) &&
        len == binary_length_z_79(decimal@pre) + 4 &&
        out_l == decorated_binary_output_z_79(decimal@pre) &&
        problem_79_spec_z(decimal@pre, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int bits = 0;
    int x = decimal;
    char* out = 0;
    int pos = 0;
    int divisor = 1;
    int i = 1;
    if (decimal == 0) {
        out = malloc_char_array(6);
        out[0] = 100;
        out[1] = 98;
        out[2] = 48;
        out[3] = 100;
        out[4] = 98;
        out[5] = 0;
        return out;
    }

    /*@ Inv Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        0 <= x &&
        0 <= bits &&
        out == 0 &&
        pos == 0 &&
        divisor == 1 &&
        i == 1 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
        binary_count_state_z_79(decimal@pre, x, bits)
    */
    while (x > 0) {
        bits += 1;
        x = x / 2;
    }

    /*@ Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        out == 0 &&
        pos == 0 &&
        divisor == 1 &&
        i == 1 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX
    */

    /*@ Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        1 <= bits &&
        out == 0 &&
        pos == 0 &&
        divisor == 1 &&
        i == 1 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
        binary_divisor_state_z_79(decimal@pre, i, divisor)
    */

    /*@ Inv Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        1 <= bits &&
        out == 0 &&
        pos == 0 &&
        1 <= i && i <= bits &&
        1 <= divisor && divisor <= INT_MAX &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
        binary_divisor_state_z_79(decimal@pre, i, divisor)
    */
    while (i < bits) {
        /*@ Assert
            decimal == decimal@pre &&
            0 < decimal && decimal <= INT_MAX &&
            x == 0 &&
            bits == binary_length_z_79(decimal@pre) &&
            1 <= bits &&
            out == 0 &&
            pos == 0 &&
            1 <= i && i < bits &&
            1 <= divisor && divisor <= INT_MAX &&
            divisor * 2 <= INT_MAX &&
            problem_79_pre_z(decimal@pre) &&
            binary_safe_79(decimal@pre) &&
            binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
            binary_divisor_state_z_79(decimal@pre, i, divisor)
        */
        divisor = divisor * 2;
        i = i + 1;
    }

    /*@ Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        i == bits &&
        1 <= bits &&
        1 <= divisor && divisor <= INT_MAX &&
        out == 0 &&
        pos == 0 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
        binary_divisor_state_z_79(decimal@pre, bits, divisor)
    */

    out = malloc_char_array(bits + 5);
    /*@ Assert
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        1 <= bits &&
        i == bits &&
        1 <= divisor && divisor <= INT_MAX &&
        binary_divisor_state_z_79(decimal@pre, bits, divisor) &&
        out != 0 &&
        pos == 0 &&
        0 < bits + 5 && bits + 5 < INT_MAX &&
        1 < bits + 5 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        CharArray::undef_full(out, bits + 5)
    */

    out[0] = 100;
    out[1] = 98;
    pos = 2;

    /*@ Assert exists out_l,
        decimal == decimal@pre &&
        0 < decimal && decimal <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        i == bits &&
        1 <= divisor && divisor <= INT_MAX &&
        pos == 2 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_write_state_z_79(decimal@pre, decimal, divisor, pos, out_l) &&
        Zlength(out_l) == pos &&
        CharArray::full(out, pos, out_l) *
        CharArray::undef_seg(out, pos, bits + 5)
    */

    /*@ Inv Assert exists out_l,
        0 <= decimal &&
        decimal <= decimal@pre &&
        0 < decimal@pre && decimal@pre <= INT_MAX &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        i == bits &&
        0 <= divisor && divisor <= INT_MAX &&
        2 <= pos && pos <= bits + 2 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_length_z_79(decimal@pre) + 5 < INT_MAX &&
        binary_write_state_z_79(decimal@pre, decimal, divisor, pos, out_l) &&
        Zlength(out_l) == pos &&
        CharArray::full(out, pos, out_l) *
        CharArray::undef_seg(out, pos, bits + 5)
    */
    while (divisor > 0) {
        if (decimal >= divisor) {
            /*@ Assert exists out_l,
                divisor <= decimal &&
                0 < divisor &&
                0 <= decimal && decimal <= decimal@pre &&
                0 < decimal@pre && decimal@pre <= INT_MAX &&
                x == 0 &&
                bits == binary_length_z_79(decimal@pre) &&
                i == bits &&
                2 <= pos && pos < bits + 5 &&
                problem_79_pre_z(decimal@pre) &&
                binary_safe_79(decimal@pre) &&
                binary_write_state_z_79(decimal@pre, decimal, divisor, pos, out_l) &&
                Zlength(out_l) == pos &&
                CharArray::full(out, pos, out_l) *
                CharArray::undef_seg(out, pos, bits + 5)
            */
            out[pos] = 49;
            decimal = decimal - divisor;
            pos = pos + 1;
            /*@ Assert exists out_l,
                0 <= decimal && decimal <= decimal@pre &&
                0 < decimal@pre && decimal@pre <= INT_MAX &&
                0 < divisor && divisor <= INT_MAX &&
                x == 0 &&
                bits == binary_length_z_79(decimal@pre) &&
                i == bits &&
                2 <= pos && pos <= bits + 2 &&
                problem_79_pre_z(decimal@pre) &&
                binary_safe_79(decimal@pre) &&
                binary_write_state_z_79(decimal@pre, decimal, divisor / 2, pos, out_l) &&
                Zlength(out_l) == pos &&
                CharArray::full(out, pos, out_l) *
                CharArray::undef_seg(out, pos, bits + 5)
            */
            divisor = divisor / 2;
        } else {
            /*@ Assert exists out_l,
                decimal < divisor &&
                0 < divisor &&
                0 <= decimal && decimal <= decimal@pre &&
                0 < decimal@pre && decimal@pre <= INT_MAX &&
                x == 0 &&
                bits == binary_length_z_79(decimal@pre) &&
                i == bits &&
                2 <= pos && pos < bits + 5 &&
                problem_79_pre_z(decimal@pre) &&
                binary_safe_79(decimal@pre) &&
                binary_write_state_z_79(decimal@pre, decimal, divisor, pos, out_l) &&
                Zlength(out_l) == pos &&
                CharArray::full(out, pos, out_l) *
                CharArray::undef_seg(out, pos, bits + 5)
            */
            out[pos] = 48;
            pos = pos + 1;
            /*@ Assert exists out_l,
                0 <= decimal && decimal <= decimal@pre &&
                0 < decimal@pre && decimal@pre <= INT_MAX &&
                0 < divisor && divisor <= INT_MAX &&
                x == 0 &&
                bits == binary_length_z_79(decimal@pre) &&
                i == bits &&
                2 <= pos && pos <= bits + 2 &&
                problem_79_pre_z(decimal@pre) &&
                binary_safe_79(decimal@pre) &&
                binary_write_state_z_79(decimal@pre, decimal, divisor / 2, pos, out_l) &&
                Zlength(out_l) == pos &&
                CharArray::full(out, pos, out_l) *
                CharArray::undef_seg(out, pos, bits + 5)
            */
            divisor = divisor / 2;
        }
    }

    /*@ Assert exists out_l,
        0 <= decimal &&
        decimal <= decimal@pre &&
        divisor == 0 &&
        x == 0 &&
        bits == binary_length_z_79(decimal@pre) &&
        i == bits &&
        out_l == app(cons(100, cons(98, nil)), binary_payload_z_79(decimal@pre)) &&
        pos == bits + 2 &&
        problem_79_pre_z(decimal@pre) &&
        binary_safe_79(decimal@pre) &&
        binary_write_state_z_79(decimal@pre, decimal, divisor, pos, out_l) &&
        Zlength(out_l) == pos &&
        CharArray::full(out, pos, out_l) *
        CharArray::undef_seg(out, pos, bits + 5)
    */

    out[pos] = 100;
    pos = pos + 1;
    out[pos] = 98;
    pos = pos + 1;
    out[pos] = 0;

    return out;
}
