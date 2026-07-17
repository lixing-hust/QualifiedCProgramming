/*
Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    digitSum("") => 0
    digitSum("abAB") => 131
    digitSum("abcCd") => 67
    digitSum("helloE") => 69
    digitSum("woArBld") => 131
    digitSum("aAaaaXa") => 153
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_66_pre_z: list Z -> Prop)
               (problem_66_spec_z: list Z -> Z -> Prop)
               (upper_sum_prefix_66: Z -> list Z -> Z)
               (upper_sum_safe_66: list Z -> Prop) */
/*@ Import Coq Require Import coins_66 */

int digitSum(char *s)
/*@ With input
    Require
        valid_string(input) &&
        problem_66_pre_z(input) &&
        string_length(input) < INT_MAX &&
        upper_sum_safe_66(input) &&
        store_string(s, input)
    Ensure
        problem_66_spec_z(input, __return) &&
        store_string(s, input)
*/
{
    int sum = 0;
    int n = strlen(s) /*@ where str = input */;
    int i;

    /*@ Inv Assert
        s == s@pre &&
        n == string_length(input) &&
        valid_string(input) &&
        problem_66_pre_z(input) &&
        string_length(input) < INT_MAX &&
        upper_sum_safe_66(input) &&
        0 <= i && i <= n &&
        sum == upper_sum_prefix_66(i, input) &&
        store_string(s@pre, input)
    */
    for (i = 0; i < n; i++) {
        int ch = s[i];
        if (ch >= 65 && ch <= 90) {
            sum += ch;
        }
    }
    return sum;
}
