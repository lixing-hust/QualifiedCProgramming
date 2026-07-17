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
#include "string.h"

/*@ Extern Coq (problem_56_pre_z: list Z -> Prop)
               (problem_56_spec_z: list Z -> Z -> Prop)
               (bracket_state_56: list Z -> Z -> Z -> Prop)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_56 */

int correct_bracketing(char *brackets)
/*@ With input_l (brackets0: Z)
    Require
        brackets == brackets0 &&
        valid_string(input_l) &&
        problem_56_pre_z(input_l) &&
        string_length(input_l) + 1 < INT_MAX &&
        store_string(brackets, input_l)
    Ensure
        problem_56_spec_z(input_l, __return) &&
        store_string(brackets0, input_l)
*/
{
    int level = 0;
    int n = strlen(brackets) /*@ where str = input_l */;
    int i;

    /*@ Inv Assert
        brackets == brackets0 &&
        n == string_length(input_l) &&
        0 <= i && i <= n &&
        0 <= level && level <= i &&
        valid_string(input_l) &&
        problem_56_pre_z(input_l) &&
        string_length(input_l) + 1 < INT_MAX &&
        bracket_state_56(input_l, i, level) &&
        store_string(brackets, input_l)
    */
    for (i = 0; i < n; i = i + 1) {
        {
            int ch = brackets[i];
            if (ch == '<') {
                level = level + 1;
            }
            if (ch == '>') {
                level = level - 1;
            }
            if (level < 0) {
                return 0;
            }
        }
        /*@ Assert
            brackets == brackets0 &&
            n == string_length(input_l) &&
            0 <= i && i < n &&
            0 <= level && level <= i + 1 &&
            valid_string(input_l) &&
            problem_56_pre_z(input_l) &&
            string_length(input_l) + 1 < INT_MAX &&
            bracket_state_56(input_l, i + 1, level) &&
            store_string(brackets, input_l)
        */
    }
    if (level != 0) {
        return 0;
    }
    return 1;
}
