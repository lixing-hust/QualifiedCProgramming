/*
Check if two words have the same characters.
>>> same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> same_chars("abcd", "dddddddabc")
true
>>> same_chars("dddddddabc", "abcd")
true
>>> same_chars("eabcd", "dddddddabc")
false
>>> same_chars("abcd", "dddddddabce")
false
>>> same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_54_pre_z: list Z -> list Z -> Prop)
               (problem_54_spec_z: list Z -> list Z -> Z -> Prop)
               (no_zero_z: list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (char_in_z: Z -> list Z -> Prop)
               (same_chars_prefix_z: Z -> list Z -> list Z -> Prop)
               (same_chars_all_z: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_54 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

char *strchr(char *s, int c)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure ((__return == 0 && ! char_in_z(c, l)) ||
            (__return != 0 && char_in_z(c, l))) &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int same_chars(char *s0, char *s1)
/*@ With l0 n0 l1 n1
    Require 0 <= n0 && n0 < INT_MAX &&
            0 <= n1 && n1 < INT_MAX &&
            Zlength(l0) == n0 &&
            Zlength(l1) == n1 &&
            problem_54_pre_z(l0, l1) &&
            ascii_range_z(l0) &&
            ascii_range_z(l1) &&
            no_zero_z(l0) &&
            no_zero_z(l1) &&
            CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
            CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
    Ensure problem_54_spec_z(l0, l1, __return) &&
           CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
           CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
*/
{
    int len0 = strlen(s0) /*@ where l = l0, n = n0 */;
    int len1 = strlen(s1) /*@ where l = l1, n = n1 */;
    int i;

    /*@ Inv Assert
        s0 == s0@pre && s1 == s1@pre &&
        len0 == n0 && len1 == n1 &&
        Zlength(l0) == n0 && Zlength(l1) == n1 &&
        problem_54_pre_z(l0, l1) &&
        ascii_range_z(l0) && ascii_range_z(l1) &&
        no_zero_z(l0) && no_zero_z(l1) &&
        0 <= i && i <= len0 &&
        same_chars_prefix_z(i, l0, l1) &&
        CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
    */
    for (i = 0; i < len0; i++)
    {
        int chr = s0[i];
        char *found = strchr(s1, chr) /*@ where l = l1, n = n1 */;
        if (found == 0) {
            return 0;
        }
    }

    /*@ Inv Assert
        s0 == s0@pre && s1 == s1@pre &&
        len0 == n0 && len1 == n1 &&
        Zlength(l0) == n0 && Zlength(l1) == n1 &&
        problem_54_pre_z(l0, l1) &&
        ascii_range_z(l0) && ascii_range_z(l1) &&
        no_zero_z(l0) && no_zero_z(l1) &&
        same_chars_all_z(l0, l1) &&
        0 <= i && i <= len1 &&
        same_chars_prefix_z(i, l1, l0) &&
        CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
    */
    for (i = 0; i < len1; i++)
    {
        int chr = s1[i];
        char *found = strchr(s0, chr) /*@ where l = l0, n = n0 */;
        if (found == 0) {
            return 0;
        }
    }
    return 1;
}
