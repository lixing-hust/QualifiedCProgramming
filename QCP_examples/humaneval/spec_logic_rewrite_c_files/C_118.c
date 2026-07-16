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
#include "string.h"

/*@ Extern Coq (problem_118_pre_z: list Z -> Prop)
               (problem_118_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (is_vowel_z_118: Z -> Prop)
               (alpha_codes_z_118: list Z -> Prop)
               (closest_vowel_candidate_z_118: list Z -> Z -> Prop)
               (no_candidate_after_z_118: list Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_118 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int is_vowel_code_118(int ch)
/*@ Require 0 <= ch && ch <= 127 && emp
    Ensure ((__return == 1 && is_vowel_z_118(ch@pre)) ||
            (__return == 0 && ! is_vowel_z_118(ch@pre))) && emp
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
/*@ With input
    Require
        valid_string(input) &&
        all_ascii(input) &&
        problem_118_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(word, input)
    Ensure exists output,
        problem_118_spec_z(input, output) &&
        store_string(word, input) *
        store_string(__return, output)
*/
{
    int n = strlen(word) /*@ where str = input */;
    char *out = 0;

    /*@ Assert
        word == word@pre &&
        n == string_length(input) &&
        out == 0 &&
        valid_string(input) &&
        all_ascii(input) &&
        problem_118_pre_z(input) &&
        ascii_range_z(input) &&
        alpha_codes_z_118(input) &&
        string_length(input) < INT_MAX &&
        store_string(word@pre, input)
    */
    if (n < 3) {
        out = malloc_char_array(1);
        if (out == 0) {
            return 0;
        }
        out[0] = 0;
        return out;
    }

    int i;
    int cur = 0;
    int right = 0;
    int left = 0;
    int cur_vowel = 0;
    int right_vowel = 0;
    int left_vowel = 0;
    i = n - 2;
    /*@ Inv Assert
        word == word@pre &&
        n == string_length(input) &&
        out == 0 &&
        cur == cur && right == right && left == left &&
        cur_vowel == cur_vowel &&
        right_vowel == right_vowel &&
        left_vowel == left_vowel &&
        3 <= n && n < INT_MAX &&
        0 <= i && i <= n - 2 &&
        valid_string(input) &&
        all_ascii(input) &&
        problem_118_pre_z(input) &&
        ascii_range_z(input) &&
        alpha_codes_z_118(input) &&
        no_candidate_after_z_118(input, i) &&
        store_string(word@pre, input)
    */
    while (i >= 1) {
        cur = word[i];
        right = word[i + 1];
        left = word[i - 1];
        cur_vowel = is_vowel_code_118(cur);
        if (cur_vowel == 1) {
            right_vowel = is_vowel_code_118(right);
            if (right_vowel == 0) {
                left_vowel = is_vowel_code_118(left);
                if (left_vowel == 0) {
                    /*@ Assert
                        word == word@pre &&
                        n == string_length(input) &&
                        out == 0 &&
                        cur == Znth(i, input, 0) &&
                        right == right && left == left &&
                        cur_vowel == cur_vowel &&
                        right_vowel == right_vowel &&
                        left_vowel == left_vowel &&
                        3 <= n && n < INT_MAX &&
                        1 <= i && i <= n - 2 &&
                        valid_string(input) &&
                        all_ascii(input) &&
                        problem_118_pre_z(input) &&
                        ascii_range_z(input) &&
                        alpha_codes_z_118(input) &&
                        closest_vowel_candidate_z_118(input, i) &&
                        no_candidate_after_z_118(input, i) &&
                        store_string(word@pre, input)
                    */
                    out = malloc_char_array(2);
                    if (out == 0) {
                        return 0;
                    }
                    out[0] = cur;
                    out[1] = 0;
                    return out;
                }
            }
        }
        /*@ Assert
            word == word@pre &&
            n == string_length(input) &&
            out == 0 &&
            cur == cur && right == right && left == left &&
            cur_vowel == cur_vowel &&
            right_vowel == right_vowel &&
            left_vowel == left_vowel &&
            3 <= n && n < INT_MAX &&
            1 <= i && i <= n - 2 &&
            valid_string(input) &&
            all_ascii(input) &&
            problem_118_pre_z(input) &&
            ascii_range_z(input) &&
            alpha_codes_z_118(input) &&
            ! closest_vowel_candidate_z_118(input, i) &&
            no_candidate_after_z_118(input, i) &&
            store_string(word@pre, input)
        */
        i -= 1;
    }

    /*@ Assert
        word == word@pre &&
        n == string_length(input) &&
        out == 0 &&
        cur == cur && right == right && left == left &&
        cur_vowel == cur_vowel &&
        right_vowel == right_vowel &&
        left_vowel == left_vowel &&
        i == 0 &&
        valid_string(input) &&
        all_ascii(input) &&
        problem_118_pre_z(input) &&
        ascii_range_z(input) &&
        alpha_codes_z_118(input) &&
        no_candidate_after_z_118(input, 0) &&
        store_string(word@pre, input)
    */
    out = malloc_char_array(1);
    if (out == 0) {
        return 0;
    }
    out[0] = 0;
    return out;
}
