/*
remove_vowels is a function that takes string && returns string without vowels.
>>> remove_vowels("")
""
>>> remove_vowels("abcdef\nghijklm")
"bcdf\nghjklm"
>>> remove_vowels("abcdef")
"bcdf"
>>> remove_vowels("aaaaa")
""
>>> remove_vowels("aaBAA")
"B"
>>> remove_vowels("zbcd")
"zbcd"
*/
#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_51_pre_z: list Z -> Prop)
               (problem_51_spec_z: list Z -> list Z -> Prop)
               (filter_prefix_51: list Z -> Z -> list Z -> Prop)
               (vowel_payload_51: list Z)
               (vowel_literal_51: String)
               (all_vowel_literals_51: list String)
               (vowel_ptr_51: (String -> Z) -> Z)
               (vowel_payload_safe_51: Prop)
               (LitMap: String -> Z)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_51 */

char *malloc_char_array(int n)
/*@ Require 0 < n && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char *remove_vowels(char *text)
/*@ With input_l (text0: Z)
    Require
        text == text0 &&
        valid_string(input_l) &&
        problem_51_pre_z(input_l) &&
        vowel_payload_safe_51 &&
        string_length(input_l) + 1 < INT_MAX &&
        store_string(text, input_l) *
        GlobalStrings(LitMap)
    Ensure
        exists output_l,
        problem_51_spec_z(input_l, output_l) &&
        Zlength(output_l) <= string_length(input_l) &&
        store_string(text0, input_l) *
        store_string(__return, output_l) *
        CharArray::undef_seg(__return, Zlength(output_l) + 1,
                                      string_length(input_l) + 1) *
        store_string(vowel_ptr_51(LitMap), vowel_payload_51) *
        GlobalStrings_missing(LitMap, all_vowel_literals_51)
*/
{
    char *vowels = "AEIOUaeiou";
    int i;
    int j = 0;
    int n = strlen(text) /*@ where str = input_l */;
    char *out = malloc_char_array(n + 1);

    if (out == 0) {
        return 0;
    }

    /*@ Inv Assert
        exists output_l,
        text == text0 &&
        vowels == vowel_ptr_51(LitMap) &&
        n == string_length(input_l) &&
        j == Zlength(output_l) &&
        0 <= i && i <= n &&
        0 <= j && j <= i &&
        valid_string(input_l) &&
        problem_51_pre_z(input_l) &&
        vowel_payload_safe_51 &&
        filter_prefix_51(input_l, i, output_l) &&
        string_length(input_l) + 1 < INT_MAX &&
        store_string(text, input_l) *
        CharArray::full(out, j, output_l) *
        CharArray::undef_seg(out, j, n + 1) *
        store_string(vowels, vowel_payload_51) *
        GlobalStrings_missing(LitMap, all_vowel_literals_51)
    */
    for (i = 0; i < n; i++) {
        int ch = text[i];
        char *found = strchr(vowels, ch) /*@ where str = vowel_payload_51 */;
        if (found == 0) {
            out[j] = ch;
            j = j + 1;
        }
    }
    out[j] = 0;
    return out;
}
