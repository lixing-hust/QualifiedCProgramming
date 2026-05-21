/*
remove_vowels is a function that takes string && returns string without vowels.
>>> remove_vowels("")
""
>>> remove_vowels("abcdef\nghijklm")
"bcdf\nghjklm"
>>> remove_vowels("abcdef")
"bcdf"
>>> remove_vowels("aaaaa")
""
>>> remove_vowels("aaBAA")
"B"
>>> remove_vowels("zbcd")
"zbcd"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_51_pre_z: list Z -> Prop)
               (problem_51_spec_z: list Z -> list Z -> Prop)
               (remove_vowels_prefix_z: Z -> list Z -> list Z)
               (char_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_51 */

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

char *remove_vowels(char *text)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_51_pre_z(l) &&
            char_range_z(l) &&
            CharArray::full(text, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l out_len,
            0 <= out_len && out_len <= len &&
            Zlength(out_l) == out_len &&
            problem_51_spec_z(l, out_l) &&
            CharArray::full(text, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, out_len + 1, app(out_l, cons(0, nil))) *
            CharArray::undef_seg(__return, out_len + 1, len + 1)
*/
{
    int i;
    int j = 0;
    int n = strlen(text) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 1);

    /*@ Inv Assert
        exists out_l,
        text == text@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_51_pre_z(l) &&
        char_range_z(l) &&
        0 <= i && i <= n &&
        0 <= j && j <= i &&
        Zlength(out_l) == j &&
        out_l == remove_vowels_prefix_z(i, l) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, j, out_l) *
        CharArray::undef_seg(out, j, n + 1)
    */
    for (i = 0; i < n; i++) {
        int c = text[i];
        if (c == 65 || c == 69 || c == 73 || c == 79 || c == 85 ||
            c == 97 || c == 101 || c == 105 || c == 111 || c == 117) {
        } else {
            out[j] = c;
            j = j + 1;
        }
    }
    out[j] = 0;
    return out;
}
