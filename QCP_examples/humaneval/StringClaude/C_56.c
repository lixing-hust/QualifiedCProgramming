/*
brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("<")
false
>>> correct_bracketing("<>")
true
>>> correct_bracketing("<<><>>")
true
>>> correct_bracketing("><<>")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_56_pre_z: list Z -> Prop)
               (problem_56_spec_z: list Z -> Z -> Prop)
               (angle_level_upto: Z -> list Z -> Z)
               (angle_nonnegative_prefix: Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_56 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int correct_bracketing(char *brackets)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range_z(l) &&
        problem_56_pre_z(l) &&
        CharArray::full(brackets, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_56_spec_z(l, __return) &&
        CharArray::full(brackets, len + 1, app(l, cons(0, nil)))
*/
{
    int level = 0;
    int n = strlen(brackets) /*@ where l = l, n = len */;
    int i;
    /*@ Inv Assert
        brackets == brackets@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        ascii_range_z(l) &&
        problem_56_pre_z(l) &&
        0 <= i && i <= n &&
        0 <= level && level <= i &&
        level == angle_level_upto(i, l) &&
        angle_nonnegative_prefix(i, l) &&
        CharArray::full(brackets, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (brackets[i] == 60) {
            level = level + 1;
        } else if (brackets[i] == 62) {
            level = level - 1;
        }
        if (level < 0) {
            return 0;
        }
    }
    if (level != 0) {
        return 0;
    }
    return 1;
}
