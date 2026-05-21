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
#include "char_array_def.h"

/*@ Extern Coq (problem_67_pre_z: list Z -> Z -> Prop)
               (problem_67_spec_z: list Z -> Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (fruit_state_safe_z: list Z -> Prop)
               (fruit_output_safe_z: list Z -> Z -> Prop)
               (fruit_num1_prefix_z: Z -> list Z -> Z)
               (fruit_num2_prefix_z: Z -> list Z -> Z)
               (fruit_cur_prefix_z: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_67 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int fruit_distribution(char *s, int total)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            0 <= total &&
            Zlength(l) == len &&
            problem_67_pre_z(l, total) &&
            ascii_range_z(l) &&
            fruit_state_safe_z(l) &&
            fruit_output_safe_z(l, total) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure problem_67_spec_z(l, total, __return) &&
           CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int num1 = -1;
    int num2 = -1;
    int cur = -1;
    int i;
    int slen = strlen(s) /*@ where l = l, n = len */;

    /*@ Inv Assert
        s == s@pre &&
        total == total@pre &&
        0 <= total &&
        slen == len &&
        Zlength(l) == len &&
        problem_67_pre_z(l, total) &&
        ascii_range_z(l) &&
        fruit_state_safe_z(l) &&
        fruit_output_safe_z(l, total) &&
        0 <= i && i <= slen &&
        num1 == fruit_num1_prefix_z(i, l) &&
        num2 == fruit_num2_prefix_z(i, l) &&
        cur == fruit_cur_prefix_z(i, l) &&
        -1 <= num1 && num1 <= INT_MAX &&
        -1 <= num2 && num2 <= INT_MAX &&
        -1 <= cur && cur <= INT_MAX &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < slen; i++) {
        int chr = s[i];
        if (chr >= 48 && chr <= 57) {
            if (cur < 0) {
                cur = 0;
            }
            cur = cur * 10 + (chr - 48);
        } else if (cur >= 0) {
            if (num1 < 0) {
                num1 = cur;
            } else if (num2 < 0) {
                num2 = cur;
            }
            cur = -1;
        }
    }

    if (cur >= 0) {
        if (num1 < 0) {
            num1 = cur;
        } else if (num2 < 0) {
            num2 = cur;
        }
    }

    if (num1 < 0) {
        num1 = 0;
    }
    if (num2 < 0) {
        num2 = 0;
    }
    return total - num1 - num2;
}
