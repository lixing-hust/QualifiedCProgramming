/*
Create a function that takes a string as input which contains only square brackets.
The function returns true exactly when the canonical reset-on-unmatched-close scan
falls at least two levels below a previously reached depth.
*/
#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_132_pre_z: list Z -> Prop)
               (problem_132_result_z: list Z -> Z -> Prop)
               (bracket_codes_z_132: list Z -> Prop)
               (nested_scan_state_132: list Z -> Z -> Z -> Z -> Prop)
               (nested_scan_after_132: list Z -> Z -> Z -> Z -> Prop)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_132 */

int is_nested(char *str)
/*@ With input
    Require
        valid_string(input) &&
        problem_132_pre_z(input) &&
        bracket_codes_z_132(input) &&
        string_length(input) < INT_MAX &&
        store_string(str, input)
    Ensure
        problem_132_result_z(input, __return) &&
        store_string(str, input)
*/
{
    int n = strlen(str) /*@ where str = input */;
    int count = 0;
    int maxcount = 0;
    int i;
    int ch = 0;

    /*@ Inv Assert
        str == str@pre &&
        n == string_length(input) &&
        0 <= i && i <= n &&
        0 <= count && count <= maxcount && maxcount <= i &&
        0 <= ch && ch <= 127 &&
        valid_string(input) &&
        problem_132_pre_z(input) &&
        bracket_codes_z_132(input) &&
        string_length(input) < INT_MAX &&
        nested_scan_state_132(input, i, count, maxcount) &&
        store_string(str@pre, input)
    */
    for (i = 0; i < n; i++) {
        ch = str[i];
        if (ch == 91) count += 1;
        if (ch == 93) count -= 1;
        if (count < 0) count = 0;
        if (count > maxcount) maxcount = count;

        /*@ Assert
            str == str@pre &&
            n == string_length(input) &&
            0 <= i && i < n &&
            0 <= count && count <= maxcount && maxcount <= i + 1 &&
            (ch == 91 || ch == 93) &&
            valid_string(input) &&
            problem_132_pre_z(input) &&
            bracket_codes_z_132(input) &&
            string_length(input) < INT_MAX &&
            nested_scan_after_132(input, i + 1, count, maxcount) &&
            store_string(str@pre, input)
        */
        if (count <= maxcount - 2) {
            /*@ Assert
                problem_132_result_z(input, 1) &&
                store_string(str@pre, input) *
                data_at(&str, str@pre) * data_at(&n, n) *
                data_at(&count, count) * data_at(&maxcount, maxcount) *
                data_at(&i, i) * data_at(&ch, ch)
            */
            return 1;
        }
    }

    /*@ Assert
        problem_132_result_z(input, 0) &&
        store_string(str@pre, input) *
        data_at(&str, str@pre) * data_at(&n, n) *
        data_at(&count, count) * data_at(&maxcount, maxcount) *
        data_at(&i, i) * data_at(&ch, ch)
    */
    return 0;
}
