/*
Write a function vowels_count which takes a string representing a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a vowel, but only when it is at the end of the given word.

Example:
>>> vowels_count("abcde")
2
>>> vowels_count("ACEDY")
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_64_pre_z: list Z -> Prop)
               (problem_64_spec_z: list Z -> Z -> Prop)
               (vowel_count_state_64: list Z -> Z -> Z -> Prop)
               (vowel_regular_step_64: list Z -> Z -> Z -> Prop)
               (vowel_miss_step_64: list Z -> Z -> Z -> Prop)
               (vowel_final_empty_64: list Z -> Z -> Prop)
               (vowel_final_y_64: list Z -> Z -> Prop)
               (vowel_final_not_y_64: list Z -> Z -> Prop)
               (vowel_payload_64: list Z)
               (vowel_literal_64: String)
               (all_vowel_literals_64: list String)
               (vowel_ptr_64: (String -> Z) -> Z)
               (vowel_payload_safe_64: Prop)
               (vowel_literal_heap_64: (String -> Z) -> Assertion)
               (LitMap: String -> Z)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_64 */

int vowels_count(char *s)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_64_pre_z(str_l) &&
        string_length(str_l) < INT_MAX &&
        store_string(s, str_l) *
        GlobalStrings(LitMap)
    Ensure
        problem_64_spec_z(str_l, __return) &&
        store_string(s, str_l) *
        store_string(vowel_ptr_64(LitMap), vowel_payload_64) *
        GlobalStrings_missing(LitMap, all_vowel_literals_64)
*/
{
    char *vowels = "aeiouAEIOU";
    /*@ Assert
        s == s@pre &&
        vowels == vowel_ptr_64(LitMap) &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_64_pre_z(str_l) &&
        vowel_payload_safe_64 &&
        string_length(str_l) < INT_MAX &&
        store_string(s@pre, str_l) *
        store_string(vowels, vowel_payload_64) *
        GlobalStrings_missing(LitMap, all_vowel_literals_64)
    */
    int n = (int)strlen(s) /*@ where str = str_l */;
    int count = 0;
    int i;

    /*@ Inv Assert
        s == s@pre &&
        n == string_length(str_l) &&
        vowels == vowel_ptr_64(LitMap) &&
        0 <= i && i <= n &&
        0 <= count && count <= i &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_64_pre_z(str_l) &&
        vowel_payload_safe_64 &&
        string_length(str_l) < INT_MAX &&
        vowel_count_state_64(str_l, i, count) &&
        store_string(s@pre, str_l) *
        store_string(vowels, vowel_payload_64) *
        GlobalStrings_missing(LitMap, all_vowel_literals_64)
    */
    for (i = 0; i < n; i++) {
        int ch = s[i];
        char *found = strchr(vowels, ch) /*@ where str = vowel_payload_64 */;
        if (found != 0) {
            count = count + 1;
            /*@ Assert
                s == s@pre &&
                n == string_length(str_l) &&
                vowels == vowel_ptr_64(LitMap) &&
                0 <= i && i < n &&
                0 <= count && count <= i + 1 &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_64_pre_z(str_l) &&
                vowel_payload_safe_64 &&
                string_length(str_l) < INT_MAX &&
                vowel_regular_step_64(str_l, i, count) &&
                vowel_count_state_64(str_l, i + 1, count) &&
                store_string(s@pre, str_l) *
                store_string(vowels, vowel_payload_64) *
                GlobalStrings_missing(LitMap, all_vowel_literals_64) *
                data_at(&found, found)
            */
        } else {
            /*@ Assert
                s == s@pre &&
                n == string_length(str_l) &&
                vowels == vowel_ptr_64(LitMap) &&
                0 <= i && i < n &&
                0 <= count && count <= i &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_64_pre_z(str_l) &&
                vowel_payload_safe_64 &&
                string_length(str_l) < INT_MAX &&
                vowel_miss_step_64(str_l, i, count) &&
                vowel_count_state_64(str_l, i + 1, count) &&
                store_string(s@pre, str_l) *
                store_string(vowels, vowel_payload_64) *
                GlobalStrings_missing(LitMap, all_vowel_literals_64) *
                data_at(&found, found)
            */
        }
    }

    if (n > 0) {
        int ch = s[n - 1];
        if (ch == 121 || ch == 89) {
            count = count + 1;
            /*@ Assert
                s == s@pre &&
                n == string_length(str_l) &&
                vowels == vowel_ptr_64(LitMap) &&
                n > 0 &&
                0 <= count && count <= n + 1 &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_64_pre_z(str_l) &&
                vowel_payload_safe_64 &&
                string_length(str_l) < INT_MAX &&
                vowel_count_state_64(str_l, n, count - 1) &&
                vowel_final_y_64(str_l, count) &&
                problem_64_spec_z(str_l, count) &&
                store_string(s@pre, str_l) *
                store_string(vowels, vowel_payload_64) *
                GlobalStrings_missing(LitMap, all_vowel_literals_64) *
                data_at(&i, i)
            */
        } else {
            /*@ Assert
                s == s@pre &&
                n == string_length(str_l) &&
                vowels == vowel_ptr_64(LitMap) &&
                n > 0 &&
                0 <= count && count <= n &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_64_pre_z(str_l) &&
                vowel_payload_safe_64 &&
                string_length(str_l) < INT_MAX &&
                vowel_count_state_64(str_l, n, count) &&
                vowel_final_not_y_64(str_l, count) &&
                problem_64_spec_z(str_l, count) &&
                store_string(s@pre, str_l) *
                store_string(vowels, vowel_payload_64) *
                GlobalStrings_missing(LitMap, all_vowel_literals_64) *
                data_at(&i, i)
            */
        }
    } else {
        /*@ Assert
            s == s@pre &&
            n == string_length(str_l) &&
            vowels == vowel_ptr_64(LitMap) &&
            n == 0 &&
            count == 0 &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_64_pre_z(str_l) &&
            vowel_payload_safe_64 &&
            string_length(str_l) < INT_MAX &&
            vowel_count_state_64(str_l, n, count) &&
            vowel_final_empty_64(str_l, count) &&
            problem_64_spec_z(str_l, count) &&
            store_string(s@pre, str_l) *
            store_string(vowels, vowel_payload_64) *
            GlobalStrings_missing(LitMap, all_vowel_literals_64) *
            data_at(&i, i)
        */
    }
    return count;
}
