/*
Write a function vowels_count which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'. 
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example: 
>>> vowels_count("abcde") 
2 
>>> vowels_count("ACEDY") 
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_64_pre_z: list Z -> Prop)
               (problem_64_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (count_regular_vowels_upto: Z -> list Z -> Z)
               (last_y_add: list Z -> Z) */
/*@ Import Coq Require Import coins_64 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int vowels_count(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_64_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_64_spec_z(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s) /*@ where l = l, n = len */;
    int count = 0;
    int i;
    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_64_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= count && count <= i &&
        count == count_regular_vowels_upto(i, l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
            s[i] == 111 || s[i] == 117 ||
            s[i] == 65 || s[i] == 69 || s[i] == 73 ||
            s[i] == 79 || s[i] == 85) {
            count = count + 1;
        }
    }
    if (n > 0 && (s[n - 1] == 121 || s[n - 1] == 89)) {
        count = count + 1;
    }
    return count;
}
