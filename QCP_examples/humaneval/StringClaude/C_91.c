/*
You'll be given a string of words, && your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' || '!'.

For example:
>>> is_bored("Hello world")
0
>>> is_bored("The sky is blue. The sun is shining. I love this weather")
1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_91_pre_z: list Z -> Prop)
               (problem_91_spec_z: list Z -> Z -> Prop)
               (bored_sum_prefix_z: Z -> list Z -> Z)
               (bored_isstart_prefix_z: Z -> list Z -> Z)
               (bored_isi_prefix_z: Z -> list Z -> Z)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_91 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_bored(char *S)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range_z(l) &&
        problem_91_pre_z(l) &&
        CharArray::full(S, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_91_spec_z(l, __return) &&
        CharArray::full(S, len + 1, app(l, cons(0, nil)))
*/
{
    int i;
    int isstart = 1;
    int isi = 0;
    int sum = 0;
    int n = strlen(S) /*@ where l = l, n = len */;

    /*@ Inv Assert
        S == S@pre &&
        n == len &&
        Zlength(l) == len &&
        ascii_range_z(l) &&
        problem_91_pre_z(l) &&
        0 <= i && i <= n &&
        sum == bored_sum_prefix_z(i, l) &&
        isstart == bored_isstart_prefix_z(i, l) &&
        isi == bored_isi_prefix_z(i, l) &&
        0 <= sum && sum <= i &&
        CharArray::full(S, len + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        int chr = S[i];
        if (chr == 32 && isi == 1) {
            isi = 0;
            sum += 1;
        }
        if (chr == 73 && isstart == 1) {
            isi = 1;
        } else {
            isi = 0;
        }
        if (chr != 32) {
            isstart = 0;
        }
        if (chr == 46 || chr == 63 || chr == 33) {
            isstart = 1;
        }
    }
    return sum;
}
