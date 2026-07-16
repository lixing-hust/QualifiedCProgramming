/*
Given a string text, replace all spaces in it with underscores,
and if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example   3") == "_Example-3"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_140_pre_z: list Z -> Prop)
               (problem_140_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (flush_spaces_z_140: Z -> list Z)
               (fix_spaces_state_z_140: list Z -> list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_140 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n <= INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char *fix_spaces(char *text)
/*@ With input
    Require
        valid_string(input) &&
        problem_140_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(text, input)
    Ensure exists output,
        problem_140_spec_z(input, output) &&
        store_string(text, input) *
        store_string(__return, output) *
        CharArray::undef_seg(__return,
            string_length(output) + 1, string_length(input) + 1)
*/
{
    int n = strlen(text) /*@ where str = input */;
    char *out = malloc_char_array(n + 1);
    if (out == 0) return 0;
    int k = 0;
    int spacelen = 0;
    int i;

    /*@ Inv Assert
        exists output,
        text == text@pre &&
        n == string_length(input) &&
        0 <= i && i <= n &&
        0 <= k && 0 <= spacelen && k + spacelen <= i &&
        k == Zlength(output) &&
        fix_spaces_state_z_140(input, output, i, spacelen) &&
        valid_string(input) &&
        problem_140_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(text@pre, input) *
        CharArray::full(out, k, output) *
        CharArray::undef_seg(out, k, n + 1)
    */
    for (i = 0; i < n; i++) {
        if (text[i] == ' ') {
            spacelen += 1;
        } else {
            if (spacelen == 1) {
                out[k] = '_';
                k += 1;
            }
            if (spacelen == 2) {
                out[k] = '_';
                k += 1;
                out[k] = '_';
                k += 1;
            }
            if (spacelen > 2) {
                out[k] = '-';
                k += 1;
            }
            spacelen = 0;
            out[k] = text[i];
            k += 1;
        }
        /*@ Assert
            exists output,
            text == text@pre &&
            n == string_length(input) &&
            0 <= i && i < n &&
            0 <= k && 0 <= spacelen && k + spacelen <= i + 1 &&
            k == Zlength(output) &&
            fix_spaces_state_z_140(input, output, i + 1, spacelen) &&
            valid_string(input) &&
            problem_140_pre_z(input) &&
            ascii_range_z(input) &&
            string_length(input) < INT_MAX &&
            store_string(text@pre, input) *
            CharArray::full(out, k, output) *
            CharArray::undef_seg(out, k, n + 1)
        */
    }

    if (spacelen == 1) {
        out[k] = '_';
        k += 1;
    }
    if (spacelen == 2) {
        out[k] = '_';
        k += 1;
        out[k] = '_';
        k += 1;
    }
    if (spacelen > 2) {
        out[k] = '-';
        k += 1;
    }
    /*@ Assert
        exists prefix output,
        text == text@pre &&
        i == i &&
        n == string_length(input) &&
        0 <= k && 0 <= spacelen && k <= n &&
        k == Zlength(output) &&
        output == app(prefix, flush_spaces_z_140(spacelen)) &&
        fix_spaces_state_z_140(input, prefix, n, spacelen) &&
        valid_string(input) &&
        problem_140_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(text@pre, input) *
        CharArray::full(out, k, output) *
        CharArray::undef_seg(out, k, n + 1)
    */
    out[k] = 0;
    return out;
}
