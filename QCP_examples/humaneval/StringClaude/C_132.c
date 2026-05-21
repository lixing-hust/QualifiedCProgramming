/*
Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested("[[]]") -> true
is_nested("[]]]]]]][[[[[]") -> false
is_nested("[][]") -> false
is_nested("[]") -> false
is_nested("[[][]]") -> true
is_nested("[[]][[") -> true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_132_pre_z: list Z -> Prop)
               (problem_132_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (subseq_state_prefix_z: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_132 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_nested(char *str)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_132_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_132_spec_z(l, __return) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int state = 0;
    int i;
    int n = strlen(str) /*@ where l = l, n = len */;

    /*@ Inv Assert
        str == str@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_132_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        state == subseq_state_prefix_z(i, l) &&
        0 <= state && state <= 4 &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        int chr = str[i];
        if (state == 0) {
            if (chr == 91) {
                state = 1;
            }
        } else if (state == 1) {
            if (chr == 91) {
                state = 2;
            }
        } else if (state == 2) {
            if (chr == 93) {
                state = 3;
            }
        } else if (state == 3) {
            if (chr == 93) {
                state = 4;
            }
        }
    }
    if (state == 4) {
        return 1;
    }
    return 0;
}
