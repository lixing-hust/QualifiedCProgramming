/*
Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
prime_length("Hello") == true
prime_length("abcdcba") == true
prime_length("kittens") == true
prime_length("orange") == false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_82_pre_z: list Z -> Prop)
               (problem_82_spec_z: list Z -> Z -> Prop)
               (prime_prefix_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_82 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int prime_length(char *str)
/*@ With l len
    Require
        0 <= len && len <= 2147302921 &&
        Zlength(l) == len &&
        problem_82_pre_z(l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_82_spec_z(l, __return) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(str) /*@ where l = l, n = len */;
    if (n < 2) return 0;

    /*@ Inv Assert
        str == str@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_82_pre_z(l) &&
        2 <= n && n <= 2147302921 &&
        2 <= i && i <= 46340 &&
        prime_prefix_z(i, n) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    */
    for (i = 2; i * i <= n; i++) {
        if (n % i == 0) return 0;
    }
    return 1;
}
