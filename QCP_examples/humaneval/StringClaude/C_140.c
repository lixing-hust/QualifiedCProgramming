/*
Given a string text, replace all spaces in it with underscores,
&& if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example   3") == "_Example-3"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_140_pre_z: list Z -> Prop)
               (problem_140_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (fix_spaces_prefix_z: Z -> list Z -> list Z)
               (fix_spaces_pending_z: Z -> list Z -> Z)
               (fix_spaces_output_z: list Z -> list Z) */
/*@ Import Coq Require Import coins_140 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

char *fix_spaces(char *text)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_140_pre_z(l) &&
            ascii_range_z(l) &&
            CharArray::full(text, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l out_len,
            0 <= out_len && out_len <= len &&
            Zlength(out_l) == out_len &&
            problem_140_spec_z(l, out_l) &&
            CharArray::full(text, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, out_len + 1, app(out_l, cons(0, nil))) *
            CharArray::undef_seg(__return, out_len + 1, len + 1)
*/
{
    int n = strlen(text) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 1);
    int k = 0;
    int spacelen = 0;
    int i;

    /*@ Inv Assert
        exists out_l,
        text == text@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_140_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= k && k <= i &&
        0 <= spacelen &&
        k + spacelen <= i &&
        k == Zlength(out_l) &&
        out_l == fix_spaces_prefix_z(i, l) &&
        spacelen == fix_spaces_pending_z(i, l) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, k, out_l) *
        CharArray::undef_seg(out, k, n + 1)
    */
    for (i = 0; i < n; i++) {
        int c = text[i];
        if (c == 32) {
            spacelen = spacelen + 1;
        } else {
            if (spacelen == 1) {
                out[k] = 95;
                k = k + 1;
            } else if (spacelen == 2) {
                out[k] = 95;
                k = k + 1;
                out[k] = 95;
                k = k + 1;
            } else if (spacelen > 2) {
                out[k] = 45;
                k = k + 1;
            }
            spacelen = 0;
            out[k] = c;
            k = k + 1;
        }
    }

    if (spacelen == 1) {
        out[k] = 95;
        k = k + 1;
    } else if (spacelen == 2) {
        out[k] = 95;
        k = k + 1;
        out[k] = 95;
        k = k + 1;
    } else if (spacelen > 2) {
        out[k] = 45;
        k = k + 1;
    }

    out[k] = 0;
    return out;
}
