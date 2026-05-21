/*
Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
check_if_last_char_is_a_letter("apple pie") -> false
check_if_last_char_is_a_letter("apple pi e") -> true
check_if_last_char_is_a_letter("apple pi e ") -> false
check_if_last_char_is_a_letter("") -> false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_134_pre_z: list Z -> Prop)
               (problem_134_spec_z: list Z -> Z -> Prop)
               (is_alpha_z: Z -> Prop)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_134 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int check_if_last_char_is_a_letter(char *txt)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range_z(l) &&
        problem_134_pre_z(l) &&
        CharArray::full(txt, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_134_spec_z(l, __return) &&
        CharArray::full(txt, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(txt) /*@ where l = l, n = len */;
    if (n == 0) return 0;

    int chr = txt[n - 1];
    if (chr < 65) return 0;
    if (chr > 90 && chr < 97) return 0;
    if (chr > 122) return 0;

    if (n == 1) return 1;

    /*@ Assert
        txt == txt@pre &&
        n == len &&
        1 < n &&
        chr == Znth(n - 1, l, 0) &&
        is_alpha_z(chr) &&
        Zlength(l) == len &&
        ascii_range_z(l) &&
        problem_134_pre_z(l) &&
        CharArray::full(txt, len + 1, app(l, cons(0, nil)))
    */
    chr = txt[n - 2];
    if (chr == 32) return 1;
    return 0;
}
