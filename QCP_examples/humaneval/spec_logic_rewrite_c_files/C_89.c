/*
Create a function encrypt that takes a string as an argument &&
returns a string encrypted with the alphabet being rotated. 
The alphabet should be rotated in a manner such that the letters 
shift down by two multiplied to two places.
For example:
encrypt("hi") returns "lm"
encrypt("asdfghjkl") returns "ewhjklnop"
encrypt("gf") returns "kj"
encrypt("et") returns "ix"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_89_pre_z: list Z -> Prop)
               (problem_89_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (lowercase_codes_z_89: list Z -> Prop)
               (shift_four_z_89: Z -> Z)
               (rotate_prefix_z_89: list Z -> list Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_89 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char *encrypt(char *s)
/*@ With input
    Require
        valid_string(input) &&
        problem_89_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(s, input)
    Ensure exists output,
        problem_89_spec_z(input, output) &&
        store_string(s, input) *
        store_string(__return, output)
*/
{
    int n = strlen(s) /*@ where str = input */;
    char *out = malloc_char_array(n + 1);
    if (out == 0) {
        return 0;
    }
    int i;

    /*@ Inv Assert
        exists output,
        s == s@pre &&
        n == string_length(input) &&
        valid_string(input) &&
        problem_89_pre_z(input) &&
        ascii_range_z(input) &&
        lowercase_codes_z_89(input) &&
        string_length(input) < INT_MAX &&
        0 <= i && i <= n &&
        rotate_prefix_z_89(input, output, i) &&
        store_string(s@pre, input) *
        CharArray::full(out, i, output) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = (s[i] + 4 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
