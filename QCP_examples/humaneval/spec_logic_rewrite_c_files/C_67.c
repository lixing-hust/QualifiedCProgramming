/*
In this task, you will be given a string that represents a number of apples && oranges
that are distributed in a basket of fruit this basket contains
apples, oranges, && mango fruits. Given the string that represents the total number of
the oranges && apples && an integer that represent the total number of the fruits
in the basket return the number of the mango fruits in the basket.
for example:
fruit_distribution("5 apples && 6 oranges", 19) ->19 - 5 - 6 = 8
fruit_distribution("0 apples && 1 oranges",3) -> 3 - 0 - 1 = 2
fruit_distribution("2 apples && 3 oranges", 100) -> 100 - 2 - 3 = 95
fruit_distribution("100 apples && 1 oranges",120) -> 120 - 100 - 1 = 19
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_67_pre_z: list Z -> Z -> Prop)
               (problem_67_spec_z: list Z -> Z -> Z -> Prop)
               (fruit_safe_input_67: list Z -> Z -> Prop)
               (fruit_scan_state_67: list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (is_digit_z_67: Z -> Prop)
               (digit_value_z_67: Z -> Z)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_67 */

int fruit_distribution(char *s, int n)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        0 <= n && n <= INT_MAX &&
        problem_67_pre_z(str_l, n) &&
        fruit_safe_input_67(str_l, n) &&
        string_length(str_l) < INT_MAX &&
        store_string(s, str_l)
    Ensure
        0 <= __return && __return <= INT_MAX &&
        problem_67_spec_z(str_l, n, __return) &&
        store_string(s, str_l)
*/
{
    int len = (int)strlen(s) /*@ where str = str_l */;
    int num1 = -1;
    int num2 = -1;
    int cur = -1;
    int i;

    /*@ Inv Assert
        0 <= i && i <= len &&
        len == string_length(str_l) &&
        s == s@pre &&
        n == n@pre &&
        0 <= n && n <= INT_MAX &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_67_pre_z(str_l, n) &&
        fruit_safe_input_67(str_l, n) &&
        string_length(str_l) < INT_MAX &&
        fruit_scan_state_67(str_l, n, i, num1, num2, cur) &&
        store_string(s@pre, str_l)
    */
    for (i = 0; i < len; i++) {
        int ch = s[i];
        if (ch >= 48 && ch <= 57) {
            if (cur < 0) {
                cur = 0;
                /*@ Assert
                    0 <= i && i < len &&
                    len == string_length(str_l) &&
                    s == s@pre &&
                    n == n@pre &&
                    0 <= n && n <= INT_MAX &&
                    48 <= ch && ch <= 57 &&
                    cur == 0 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_67_pre_z(str_l, n) &&
                    fruit_safe_input_67(str_l, n) &&
                    string_length(str_l) < INT_MAX &&
                    is_digit_z_67(ch) &&
                    ch == Znth(i, c_string(str_l), 0) &&
                    fruit_scan_state_67(str_l, n, i, num1, num2, cur) &&
                    store_string(s@pre, str_l)
                */
            }
            /*@ Assert
                0 <= i && i < len &&
                len == string_length(str_l) &&
                s == s@pre &&
                ch == ch &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                48 <= ch && ch <= 57 &&
                0 <= cur &&
                0 <= cur * 10 + (ch - 48) &&
                cur * 10 + (ch - 48) <= INT_MAX &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                is_digit_z_67(ch) &&
                ch == Znth(i, c_string(str_l), 0) &&
                digit_value_z_67(ch) == ch - 48 &&
                fruit_scan_state_67(str_l, n, i, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
            cur = cur * 10 + (ch - 48);
            /*@ Assert
                0 <= i && i < len &&
                len == string_length(str_l) &&
                s == s@pre &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                48 <= ch && ch <= 57 &&
                0 <= cur && cur <= INT_MAX &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                fruit_scan_state_67(str_l, n, i + 1, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
        } else if (cur >= 0) {
            if (num1 < 0) {
                num1 = cur;
                cur = -1;
                /*@ Assert
                    0 <= i && i < len &&
                    len == string_length(str_l) &&
                    s == s@pre &&
                    n == n@pre &&
                    0 <= n && n <= INT_MAX &&
                    0 <= ch && ch <= 127 &&
                    !(48 <= ch && ch <= 57) &&
                    0 <= num1 && num1 <= INT_MAX &&
                    cur == -1 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_67_pre_z(str_l, n) &&
                    fruit_safe_input_67(str_l, n) &&
                    string_length(str_l) < INT_MAX &&
                    fruit_scan_state_67(str_l, n, i + 1, num1, num2, cur) &&
                    store_string(s@pre, str_l)
                */
            } else if (num2 < 0) {
                num2 = cur;
                cur = -1;
                /*@ Assert
                    0 <= i && i < len &&
                    len == string_length(str_l) &&
                    s == s@pre &&
                    n == n@pre &&
                    0 <= n && n <= INT_MAX &&
                    0 <= ch && ch <= 127 &&
                    !(48 <= ch && ch <= 57) &&
                    0 <= num1 && num1 <= INT_MAX &&
                    0 <= num2 && num2 <= INT_MAX &&
                    cur == -1 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_67_pre_z(str_l, n) &&
                    fruit_safe_input_67(str_l, n) &&
                    string_length(str_l) < INT_MAX &&
                    fruit_scan_state_67(str_l, n, i + 1, num1, num2, cur) &&
                    store_string(s@pre, str_l)
                */
            } else {
                cur = -1;
                /*@ Assert
                    0 <= i && i < len &&
                    len == string_length(str_l) &&
                    s == s@pre &&
                    n == n@pre &&
                    0 <= n && n <= INT_MAX &&
                    0 <= ch && ch <= 127 &&
                    !(48 <= ch && ch <= 57) &&
                    0 <= num1 && num1 <= INT_MAX &&
                    0 <= num2 && num2 <= INT_MAX &&
                    cur == -1 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_67_pre_z(str_l, n) &&
                    fruit_safe_input_67(str_l, n) &&
                    string_length(str_l) < INT_MAX &&
                    fruit_scan_state_67(str_l, n, i + 1, num1, num2, cur) &&
                    store_string(s@pre, str_l)
                */
            }
        } else {
            /*@ Assert
                0 <= i && i < len &&
                len == string_length(str_l) &&
                s == s@pre &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                0 <= ch && ch <= 127 &&
                !(48 <= ch && ch <= 57) &&
                cur < 0 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                fruit_scan_state_67(str_l, n, i + 1, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
        }
    }

    if (cur >= 0) {
        if (num1 < 0) {
            num1 = cur;
            cur = -1;
            /*@ Assert
                len == string_length(str_l) &&
                i == len &&
                s == s@pre &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                0 <= num1 && num1 <= INT_MAX &&
                cur == -1 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
        } else if (num2 < 0) {
            num2 = cur;
            cur = -1;
            /*@ Assert
                len == string_length(str_l) &&
                i == len &&
                s == s@pre &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                0 <= num1 && num1 <= INT_MAX &&
                0 <= num2 && num2 <= INT_MAX &&
                cur == -1 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
        } else {
            cur = -1;
            /*@ Assert
                len == string_length(str_l) &&
                i == len &&
                s == s@pre &&
                n == n@pre &&
                0 <= n && n <= INT_MAX &&
                0 <= num1 && num1 <= INT_MAX &&
                0 <= num2 && num2 <= INT_MAX &&
                cur == -1 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_67_pre_z(str_l, n) &&
                fruit_safe_input_67(str_l, n) &&
                string_length(str_l) < INT_MAX &&
                fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
                store_string(s@pre, str_l)
            */
        }
    }

    if (num1 < 0) {
        num1 = 0;
        /*@ Assert
            len == string_length(str_l) &&
            i == len &&
            s == s@pre &&
            n == n@pre &&
            0 <= n && n <= INT_MAX &&
            num1 == 0 &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_67_pre_z(str_l, n) &&
            fruit_safe_input_67(str_l, n) &&
            string_length(str_l) < INT_MAX &&
            fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
            store_string(s@pre, str_l)
        */
    }
    if (num2 < 0) {
        num2 = 0;
        /*@ Assert
            len == string_length(str_l) &&
            i == len &&
            s == s@pre &&
            n == n@pre &&
            0 <= n && n <= INT_MAX &&
            0 <= num1 && num1 <= INT_MAX &&
            num2 == 0 &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_67_pre_z(str_l, n) &&
            fruit_safe_input_67(str_l, n) &&
            string_length(str_l) < INT_MAX &&
            fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
            store_string(s@pre, str_l)
        */
    }

    /*@ Assert
        len == string_length(str_l) &&
        i == len &&
        s == s@pre &&
        n == n@pre &&
        0 <= n && n <= INT_MAX &&
        0 <= num1 && num1 <= INT_MAX &&
        0 <= num2 && num2 <= INT_MAX &&
        0 <= n - num1 - num2 &&
        n - num1 - num2 <= INT_MAX &&
        problem_67_spec_z(str_l, n, n - num1 - num2) &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_67_pre_z(str_l, n) &&
        fruit_safe_input_67(str_l, n) &&
        string_length(str_l) < INT_MAX &&
        fruit_scan_state_67(str_l, n, len, num1, num2, cur) &&
        store_string(s@pre, str_l)
    */
    return n - num1 - num2;
}
