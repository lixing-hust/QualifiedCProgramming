/*
Checks if given string is a palindrome
>>> is_palindrome("")
true
>>> is_palindrome("aba")
true
>>> is_palindrome("aaaaa")
true
>>> is_palindrome("zbcd")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_48_pre_z: list Z -> Prop)
               (problem_48_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_48 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_palindrome(char *text)
/*@ With l n
    Require
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_48_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
    Ensure
        problem_48_spec_z(l, __return) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int j = strlen(text) /*@ where l = l, n = n */;

    if (j == 0) {
        return 1;
    }

    j = j - 1;
    /*@ Inv Assert
        text == text@pre &&
        0 < n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_48_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= j && j < n &&
        i + j == n - 1 &&
        CharArray::full(text, n + 1, app(l, cons(0, nil))) &&
        (forall (k: Z), (0 <= k && k < i) =>
            Znth(k, l, 0) == Znth(n - 1 - k, l, 0))
    */
    while (i < j) {
        if (text[i] != text[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}
