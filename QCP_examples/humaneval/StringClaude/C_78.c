/*
You have been tasked to write a function that receives 
a hexadecimal number as a string && counts the number of hexadecimal 
digits that are primes (prime number, || a prime, is a natural number 
greater than 1 that is ! a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7, 
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct || empty string, 
&& symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_78_pre_z: list Z -> Prop)
               (problem_78_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (count_prime_hex_upto: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_78 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int hex_key(char *num)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_78_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(num, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_78_spec_z(l, __return) &&
        CharArray::full(num, len + 1, app(l, cons(0, nil)))
*/
{
    int out = 0;
    int n = strlen(num) /*@ where l = l, n = len */;
    int i;
    /*@ Inv Assert
        num == num@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_78_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= out && out <= i &&
        out == count_prime_hex_upto(i, l) &&
        CharArray::full(num, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (num[i] == 50 || num[i] == 51 || num[i] == 53 ||
            num[i] == 55 || num[i] == 66 || num[i] == 68) {
            out = out + 1;
        }
    }
    return out;
}
