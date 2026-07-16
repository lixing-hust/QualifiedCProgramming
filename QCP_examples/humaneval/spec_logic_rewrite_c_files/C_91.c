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
#include "string.h"

/*@ Extern Coq (problem_91_pre_z: list Z -> Prop)
               (problem_91_spec_z: list Z -> Z -> Prop)
               (bored_sum_prefix_z: Z -> list Z -> Z)
               (bored_isstart_prefix_z: Z -> list Z -> Z)
               (bored_isi_prefix_z: Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_91 */

int is_bored(char *S)
/*@ With input
    Require
        valid_string(input) &&
        problem_91_pre_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(S, input)
    Ensure
        problem_91_spec_z(input, __return) &&
        store_string(S, input)
*/
{
    int isstart = 1;
    int isi = 0;
    int sum = 0;
    int n = strlen(S) /*@ where str = input */;
    int i;

    /*@ Inv Assert
        S == S@pre &&
        n == string_length(input) &&
        valid_string(input) &&
        problem_91_pre_z(input) &&
        string_length(input) < INT_MAX &&
        0 <= i && i <= n &&
        sum == bored_sum_prefix_z(i, input) &&
        isstart == bored_isstart_prefix_z(i, input) &&
        isi == bored_isi_prefix_z(i, input) &&
        0 <= sum && sum <= i &&
        store_string(S@pre, input)
    */
    for (i = 0; i < n; i++) {
        int ch = S[i];
        if (ch == 32 && isi == 1) {
            isi = 0;
            sum += 1;
        }
        if (ch == 73 && isstart == 1) {
            isi = 1;
        } else {
            isi = 0;
        }
        if (ch != 32) {
            isstart = 0;
        }
        if (ch == 46 || ch == 63 || ch == 33) {
            isstart = 1;
        }
    }
    return sum;
}
