/*
You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
is_happy("a") => false
is_happy("aa") => false
is_happy("abcd") => true
is_happy("aabb") => false
is_happy("adb") => true
is_happy("xyy") => false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_80_pre_z: list Z -> Prop)
               (problem_80_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (happy_prefix_z: Z -> list Z -> Prop)
               (happy_adjacent_z: Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_80 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_happy(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_80_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_80_spec_z(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s) /*@ where l = l, n = len */;
    int i;
    if (n < 3) {
        return 0;
    }
    if (s[0] == s[1]) {
        return 0;
    }
    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        3 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_80_pre_z(l) &&
        ascii_range_z(l) &&
        2 <= i && i <= n &&
        happy_prefix_z(i, l) &&
        happy_adjacent_z(i, l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    for (i = 2; i < n; i++) {
        if (s[i] == s[i - 1]) {
            return 0;
        }
        if (s[i] == s[i - 2]) {
            return 0;
        }
    }
    return 1;
}
