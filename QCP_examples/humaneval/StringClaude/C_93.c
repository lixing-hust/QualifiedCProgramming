/*
Write a function that takes a message, && encodes in such a
way that it swaps case of all letters, replaces all vowels in
the message with the letter that appears 2 places ahead of that
vowel in the english alphabet.
Assume only letters.

Examples:
>>> encode('test")
"TGST"
>>> encode("This is a message")
'tHKS KS C MGSSCGG"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_93_pre_z: list Z -> Prop)
               (problem_93_spec_z: list Z -> list Z -> Prop)
               (encode_char_z: Z -> Z)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_93 */

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

char *encode(char *message)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_93_pre_z(l) &&
            ascii_range_z(l) &&
            CharArray::full(message, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
            Zlength(out_l) == len &&
            problem_93_spec_z(l, out_l) &&
            CharArray::full(message, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int n = strlen(message) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 1);
    int i;

    /*@ Inv Assert
        exists out_l,
        message == message@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_93_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        Zlength(out_l) == i &&
        (forall (k: Z), (0 <= k && k < i) =>
            Znth(k, out_l, 0) == encode_char_z(Znth(k, l, 0))) &&
        CharArray::full(message, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, i, out_l) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = message[i];
        if (w >= 97 && w <= 122) {
            w = w - 32;
        } else if (w >= 65 && w <= 90) {
            w = w + 32;
        }
        if (w == 65 || w == 69 || w == 73 || w == 79 || w == 85 ||
            w == 97 || w == 101 || w == 105 || w == 111 || w == 117) {
            w = w + 2;
        }
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
