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
#include "char_array_def.h"

/*@ Extern Coq (problem_66_pre_z: list Z -> Prop)
               (problem_66_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (sum_upper_upto: Z -> list Z -> Z)
               (digit_sum_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_66 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int digitSum(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_66_pre_z(l) &&
        ascii_range_z(l) &&
        digit_sum_int_range(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_66_spec_z(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int sum = 0;
    int n = strlen(s) /*@ where l = l, n = len */;
    int i;
    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_66_pre_z(l) &&
        ascii_range_z(l) &&
        digit_sum_int_range(l) &&
        0 <= i && i <= n &&
        sum == sum_upper_upto(i, l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (s[i] >= 65 && s[i] <= 90) {
            sum = sum + s[i];
        }
    }
    return sum;
}
