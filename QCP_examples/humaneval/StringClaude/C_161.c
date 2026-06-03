/*
Given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_161_pre_z: list Z -> Prop)
               (problem_161_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (contains_letter_prefix_z: Z -> list Z -> Z)
               (contains_letter_z: list Z -> Z)
               (flip_char_z: Z -> Z) */
/*@ Import Coq Require Import coins_161 */

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

char *solve(char *s)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_161_pre_z(l) &&
            ascii_range_z(l) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
            Zlength(out_l) == len &&
            problem_161_spec_z(l, out_l) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(s) /*@ where l = l, n = len */;
    int has_letter = 0;
    char *out = malloc_char_array(n + 1);

    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_161_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        has_letter == contains_letter_prefix_z(i, l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) *
        CharArray::undef_full(out, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = s[i];
        if ((w >= 65 && w <= 90) || (w >= 97 && w <= 122)) {
            has_letter = 1;
        }
    }

    if (has_letter == 1) {
        /*@ Inv Assert
            exists out_l,
            s == s@pre &&
            n == len &&
            Zlength(l) == len &&
            problem_161_pre_z(l) &&
            ascii_range_z(l) &&
            has_letter == contains_letter_z(l) &&
            has_letter == 1 &&
            0 <= i && i <= n &&
            Zlength(out_l) == i &&
            (forall (k: Z), (0 <= k && k < i) =>
                Znth(k, out_l, 0) == flip_char_z(Znth(k, l, 0))) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil))) *
            CharArray::full(out, i, out_l) *
            CharArray::undef_seg(out, i, n + 1)
        */
        for (i = 0; i < n; i++) {
            int w = s[i];
            if (w >= 65 && w <= 90) {
                w = w + 32;
            } else if (w >= 97 && w <= 122) {
                w = w - 32;
            }
            out[i] = w;
        }
    } else {
        /*@ Inv Assert
            exists out_l,
            s == s@pre &&
            n == len &&
            Zlength(l) == len &&
            problem_161_pre_z(l) &&
            ascii_range_z(l) &&
            has_letter == contains_letter_z(l) &&
            has_letter == 0 &&
            0 <= i && i <= n &&
            Zlength(out_l) == i &&
            (forall (k: Z), (0 <= k && k < i) =>
                Znth(k, out_l, 0) == Znth(n - 1 - k, l, 0)) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil))) *
            CharArray::full(out, i, out_l) *
            CharArray::undef_seg(out, i, n + 1)
        */
        for (i = 0; i < n; i++) {
            out[i] = s[n - 1 - i];
        }
    }
    out[n] = 0;
    return out;
}
