/*
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper("aBCdEf") returns 1
count_upper("abcdefg") returns 0
count_upper("dBBE") returns 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_98_pre_z: list Z -> Prop)
               (problem_98_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (count_upper_even_upto: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_98 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int count_upper(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_98_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_98_spec_z(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s) /*@ where l = l, n = len */;
    int count = 0;
    int i;
    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_98_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= count && count <= i &&
        count == count_upper_even_upto(i, l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (i % 2 == 0) {
            if (s[i] == 65 || s[i] == 69 || s[i] == 73 ||
                s[i] == 79 || s[i] == 85) {
                count = count + 1;
            }
        }
    }
    return count;
}
