/*
You are given a word. Your task is to find the closest vowel that stands between 
two consonants from the right side of the word (case sensitive).

Vowels in the beginning && ending doesn't count. Return empty string if you didn't
find any vowel met the above condition. 

You may assume that the given string contains English letter only.

Example:
get_closest_vowel("yogurt") ==> "u"
get_closest_vowel("FULL") ==> "U"
get_closest_vowel("quick") ==> ""
get_closest_vowel("ab") ==> ""
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_118_pre_z: list Z -> Prop)
               (problem_118_spec_z: list Z -> list Z -> Prop)
               (is_vowel_z: Z -> Prop)
               (is_consonant_z: Z -> Prop)
               (alpha_range_z: list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (closest_vowel_candidate_z: list Z -> Z -> Prop)
               (no_candidate_after_z: Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_118 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 &&
           CharArray::full(__return, 0, nil) *
           CharArray::undef_seg(__return, 0, n)
*/
;

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_vowel_code(int ch)
/*@ Require emp
    Ensure ((__return == 1 && is_vowel_z(ch@pre)) ||
            (__return == 0 && ! is_vowel_z(ch@pre))) &&
           emp
*/
{
    if (ch == 65) return 1;
    if (ch == 69) return 1;
    if (ch == 73) return 1;
    if (ch == 79) return 1;
    if (ch == 85) return 1;
    if (ch == 97) return 1;
    if (ch == 101) return 1;
    if (ch == 105) return 1;
    if (ch == 111) return 1;
    if (ch == 117) return 1;
    return 0;
}

char *get_closest_vowel(char *word)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_118_pre_z(l) &&
        ascii_range_z(l) &&
        alpha_range_z(l) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l out_n,
        Zlength(out_l) == out_n &&
        0 <= out_n && out_n <= 1 &&
        problem_118_spec_z(l, out_l) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, out_n + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int cur;
    int right;
    int left;
    int cur_vowel;
    int right_vowel;
    int left_vowel;
    int n = strlen(word) /*@ where l = l, n = len */;
    cur = 0;
    right = 0;
    left = 0;
    cur_vowel = 0;
    right_vowel = 0;
    left_vowel = 0;

    if (n < 3) {
        char *out = malloc_char_array(1);
        out[0] = 0;
        return out;
    }

    i = n - 2;
    /*@ Inv Assert
        word == word@pre &&
        n == len &&
        3 <= n && n < INT_MAX &&
        Zlength(l) == len &&
        problem_118_pre_z(l) &&
        ascii_range_z(l) &&
        alpha_range_z(l) &&
        cur == cur &&
        right == right &&
        left == left &&
        cur_vowel == cur_vowel &&
        right_vowel == right_vowel &&
        left_vowel == left_vowel &&
        0 <= i && i <= n - 2 &&
        no_candidate_after_z(i, l) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil)))
    */
    while (i >= 1) {
        cur = word[i];
        right = word[i + 1];
        left = word[i - 1];
        cur_vowel = is_vowel_code(cur);
        if (cur_vowel == 1) {
            right_vowel = is_vowel_code(right);
            if (right_vowel == 0) {
                left_vowel = is_vowel_code(left);
                if (left_vowel == 0) {
                    /*@ Assert
                        word == word@pre &&
                        n == len &&
                        3 <= n && n < INT_MAX &&
                        Zlength(l) == len &&
                        problem_118_pre_z(l) &&
                        ascii_range_z(l) &&
                        alpha_range_z(l) &&
                        cur == cur &&
                        right == right &&
                        left == left &&
                        cur_vowel == cur_vowel &&
                        right_vowel == right_vowel &&
                        left_vowel == left_vowel &&
                        1 <= i && i <= n - 2 &&
                        cur == Znth(i, l, 0) &&
                        right == Znth(i + 1, l, 0) &&
                        left == Znth(i - 1, l, 0) &&
                        closest_vowel_candidate_z(l, i) &&
                        no_candidate_after_z(i, l) &&
                        CharArray::full(word, len + 1, app(l, cons(0, nil)))
                    */
                    char *out = malloc_char_array(2);
                    out[0] = cur;
                    out[1] = 0;
                    return out;
                }
            }
        }
        /*@ Assert
            word == word@pre &&
            n == len &&
            3 <= n && n < INT_MAX &&
            Zlength(l) == len &&
            problem_118_pre_z(l) &&
            ascii_range_z(l) &&
            alpha_range_z(l) &&
            cur == cur &&
            right == right &&
            left == left &&
            cur_vowel == cur_vowel &&
            right_vowel == right_vowel &&
            left_vowel == left_vowel &&
            1 <= i && i <= n - 2 &&
            ! closest_vowel_candidate_z(l, i) &&
            no_candidate_after_z(i, l) &&
            CharArray::full(word, len + 1, app(l, cons(0, nil)))
        */
        i -= 1;
    }

    /*@ Assert
        word == word@pre &&
        n == len &&
        3 <= n && n < INT_MAX &&
        Zlength(l) == len &&
        problem_118_pre_z(l) &&
        ascii_range_z(l) &&
        alpha_range_z(l) &&
        cur == cur &&
        right == right &&
        left == left &&
        cur_vowel == cur_vowel &&
        right_vowel == right_vowel &&
        left_vowel == left_vowel &&
        i == 0 &&
        no_candidate_after_z(0, l) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil)))
    */
    char *out = malloc_char_array(1);
    out[0] = 0;
    return out;
}
