/*
brackets is a string of '(' and ')'.
return true if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
false
>>> correct_bracketing("()")
true
>>> correct_bracketing("(()())")
true
>>> correct_bracketing(")(()")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_61_pre_z: list Z -> Prop)
               (problem_61_spec_z: list Z -> bool -> Prop)
               (bracket_state_61: list Z -> Z -> Z -> Prop)
               (string_length: list Z -> Z)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import coins_61 */

int correct_bracketing(char *brackets)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_61_pre_z(str_l) &&
        string_length(str_l) < INT_MAX &&
        store_string(brackets, str_l)
    Ensure
        ((__return != 0 && problem_61_spec_z(str_l, true)) ||
         (__return == 0 && problem_61_spec_z(str_l, false))) &&
        store_string(brackets, str_l)
*/
{
    int n = (int)strlen(brackets) /*@ where str = str_l */;
    int level = 0;
    int ch = 0;
    int i;

    /*@ Inv Assert
        0 <= i && i <= n &&
        n == string_length(str_l) &&
        brackets == brackets@pre &&
        0 <= level && level <= i &&
        0 <= ch && ch <= 127 &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_61_pre_z(str_l) &&
        string_length(str_l) < INT_MAX &&
        bracket_state_61(str_l, i, level) &&
        store_string(brackets@pre, str_l)
    */
    for (i = 0; i < n; i++) {
        ch = brackets[i];
        if (ch == 40) {
            level = level + 1;
            /*@ Assert
                0 <= i && i < n &&
                n == string_length(str_l) &&
                brackets == brackets@pre &&
                1 <= level && level <= i + 1 &&
                ch == 40 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_61_pre_z(str_l) &&
                string_length(str_l) < INT_MAX &&
                bracket_state_61(str_l, i + 1, level) &&
                store_string(brackets@pre, str_l)
            */
        } else {
            level = level - 1;
            if (level < 0) {
                /*@ Assert
                    0 <= i && i < n &&
                    n == string_length(str_l) &&
                    brackets == brackets@pre &&
                    level == -1 &&
                    ch == 41 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_61_pre_z(str_l) &&
                    string_length(str_l) < INT_MAX &&
                    problem_61_spec_z(str_l, false) &&
                    store_string(brackets@pre, str_l)
                */
                return 0;
            }
            /*@ Assert
                0 <= i && i < n &&
                n == string_length(str_l) &&
                brackets == brackets@pre &&
                0 <= level && level <= i &&
                ch == 41 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_61_pre_z(str_l) &&
                string_length(str_l) < INT_MAX &&
                bracket_state_61(str_l, i + 1, level) &&
                store_string(brackets@pre, str_l)
            */
        }
    }
    if (level != 0) {
        /*@ Assert
            n == string_length(str_l) &&
            brackets == brackets@pre &&
            level != 0 &&
            0 < level &&
            ch == ch &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_61_pre_z(str_l) &&
            string_length(str_l) < INT_MAX &&
            bracket_state_61(str_l, n, level) &&
            problem_61_spec_z(str_l, false) &&
            store_string(brackets@pre, str_l) *
            data_at(&i, i)
        */
        return 0;
    }
    /*@ Assert
        n == string_length(str_l) &&
        brackets == brackets@pre &&
        level == 0 &&
        ch == ch &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_61_pre_z(str_l) &&
        string_length(str_l) < INT_MAX &&
        bracket_state_61(str_l, n, 0) &&
        problem_61_spec_z(str_l, true) &&
        store_string(brackets@pre, str_l) *
        data_at(&i, i)
    */
    return 1;
}
