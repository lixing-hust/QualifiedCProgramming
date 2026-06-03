/*
You are given a vector of two strings, both strings consist of open
parentheses '(' || close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if && only if all parentheses in S
are balanced. For example: the string "(())()" is good, while the string
"())" is !.
Return "Yes" if there's a way to make a good string, && return "No" otherwise.

Examples:
match_parens({"()(", ")"}) == "Yes"
match_parens({")", ")"}) == "No"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_119_pre_z: list Z -> list Z -> Prop)
               (problem_119_spec_z: list Z -> list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (paren_level_upto: Z -> list Z -> Z)
               (paren_good_prefix_flag: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_119 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int match_parens(char *s1, char *s2)
/*@ With l1 l2 len1 len2
    Require
        0 <= len1 && len1 < INT_MAX &&
        0 <= len2 && len2 < INT_MAX &&
        len1 + len2 < INT_MAX &&
        Zlength(l1) == len1 &&
        Zlength(l2) == len2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        CharArray::full(s1, len1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, len2 + 1, app(l2, cons(0, nil)))
    Ensure
        problem_119_spec_z(l1, l2, __return) &&
        CharArray::full(s1, len1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, len2 + 1, app(l2, cons(0, nil)))
*/
{
    int i;
    int count = 0;
    int can = 1;
    int n1 = strlen(s1) /*@ where l = l1, n = len1 */;
    int n2 = strlen(s2) /*@ where l = l2, n = len2 */;

    /*@ Inv Assert
        s1 == s1@pre &&
        s2 == s2@pre &&
        n1 == len1 &&
        n2 == len2 &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        n1 + n2 < INT_MAX &&
        Zlength(l1) == n1 &&
        Zlength(l2) == n2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        0 <= i && i <= n1 &&
        -i <= count && count <= i &&
        count == paren_level_upto(i, app(l1, l2)) &&
        can == paren_good_prefix_flag(i, app(l1, l2)) &&
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, n2 + 1, app(l2, cons(0, nil)))
    */
    for (i = 0; i < n1; i++) {
        if (s1[i] == 40) {
            count += 1;
        } else if (s1[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    /*@ Inv Assert
        s1 == s1@pre &&
        s2 == s2@pre &&
        n1 == len1 &&
        n2 == len2 &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        n1 + n2 < INT_MAX &&
        Zlength(l1) == n1 &&
        Zlength(l2) == n2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        0 <= i && i <= n2 &&
        -(n1 + i) <= count && count <= n1 + i &&
        count == paren_level_upto(n1 + i, app(l1, l2)) &&
        can == paren_good_prefix_flag(n1 + i, app(l1, l2)) &&
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, n2 + 1, app(l2, cons(0, nil)))
    */
    for (i = 0; i < n2; i++) {
        if (s2[i] == 40) {
            count += 1;
        } else if (s2[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    if (count != 0) return 0;
    if (can == 1) return 1;

    /*@ Assert
        s1 == s1@pre &&
        s2 == s2@pre &&
        n1 == len1 &&
        n2 == len2 &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        n1 + n2 < INT_MAX &&
        Zlength(l1) == n1 &&
        Zlength(l2) == n2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        count == 0 &&
        can == 0 &&
        i == n2 &&
        paren_level_upto(n1 + n2, app(l1, l2)) == 0 &&
        paren_good_prefix_flag(n1 + n2, app(l1, l2)) == 0 &&
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, n2 + 1, app(l2, cons(0, nil)))
    */

    count = 0;
    can = 1;

    /*@ Inv Assert
        s1 == s1@pre &&
        s2 == s2@pre &&
        n1 == len1 &&
        n2 == len2 &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        n1 + n2 < INT_MAX &&
        Zlength(l1) == n1 &&
        Zlength(l2) == n2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        paren_level_upto(n1 + n2, app(l1, l2)) == 0 &&
        paren_good_prefix_flag(n1 + n2, app(l1, l2)) == 0 &&
        0 <= i && i <= n2 &&
        -i <= count && count <= i &&
        count == paren_level_upto(i, app(l2, l1)) &&
        can == paren_good_prefix_flag(i, app(l2, l1)) &&
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, n2 + 1, app(l2, cons(0, nil)))
    */
    for (i = 0; i < n2; i++) {
        if (s2[i] == 40) {
            count += 1;
        } else if (s2[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    /*@ Inv Assert
        s1 == s1@pre &&
        s2 == s2@pre &&
        n1 == len1 &&
        n2 == len2 &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        n1 + n2 < INT_MAX &&
        Zlength(l1) == n1 &&
        Zlength(l2) == n2 &&
        problem_119_pre_z(l1, l2) &&
        ascii_range_z(l1) &&
        ascii_range_z(l2) &&
        paren_level_upto(n1 + n2, app(l1, l2)) == 0 &&
        paren_good_prefix_flag(n1 + n2, app(l1, l2)) == 0 &&
        0 <= i && i <= n1 &&
        -(n2 + i) <= count && count <= n2 + i &&
        count == paren_level_upto(n2 + i, app(l2, l1)) &&
        can == paren_good_prefix_flag(n2 + i, app(l2, l1)) &&
        CharArray::full(s1, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(s2, n2 + 1, app(l2, cons(0, nil)))
    */
    for (i = 0; i < n1; i++) {
        if (s1[i] == 40) {
            count += 1;
        } else if (s1[i] == 41) {
            count -= 1;
        }
        if (count < 0) can = 0;
    }

    if (can == 1) return 1;
    return 0;
}
