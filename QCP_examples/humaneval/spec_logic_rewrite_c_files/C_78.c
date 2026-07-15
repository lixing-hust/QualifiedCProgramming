/*
You have been tasked to write a function that receives
a hexadecimal number as a string and counts the number of hexadecimal
digits that are primes.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_78_pre_z: list Z -> Prop)
               (problem_78_spec_z: list Z -> Z -> Prop)
               (hex_count_safe_78: list Z -> Prop)
               (hex_count_state_78: list Z -> Z -> Z -> Prop)
               (hex_hit_step_78: list Z -> Z -> Z -> Prop)
               (hex_miss_step_78: list Z -> Z -> Z -> Prop)
               (hex_final_78: list Z -> Z -> Prop)
               (key_payload_78: list Z)
               (key_literal_78: String)
               (all_key_literals_78: list String)
               (key_ptr_78: (String -> Z) -> Z)
               (key_payload_safe_78: Prop)
               (key_literal_heap_78: (String -> Z) -> Assertion)
               (LitMap: String -> Z)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_78 */

int hex_key(char *num)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_78_pre_z(str_l) &&
        hex_count_safe_78(str_l) &&
        key_payload_safe_78 &&
        string_length(str_l) < INT_MAX &&
        store_string(num, str_l) *
        GlobalStrings(LitMap)
    Ensure
        problem_78_spec_z(str_l, __return) &&
        store_string(num, str_l) *
        store_string(key_ptr_78(LitMap), key_payload_78) *
        GlobalStrings_missing(LitMap, all_key_literals_78)
*/
{
    char *key = "2357BD";
    /*@ Assert
        num == num@pre &&
        key == key_ptr_78(LitMap) &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_78_pre_z(str_l) &&
        hex_count_safe_78(str_l) &&
        key_payload_safe_78 &&
        string_length(str_l) < INT_MAX &&
        store_string(num@pre, str_l) *
        store_string(key, key_payload_78) *
        GlobalStrings_missing(LitMap, all_key_literals_78)
    */
    int n = (int)strlen(num) /*@ where str = str_l */;
    int out = 0;
    int i;

    /*@ Inv Assert
        num == num@pre &&
        key == key_ptr_78(LitMap) &&
        n == string_length(str_l) &&
        0 <= i && i <= n &&
        0 <= out && out <= i &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_78_pre_z(str_l) &&
        hex_count_safe_78(str_l) &&
        key_payload_safe_78 &&
        string_length(str_l) < INT_MAX &&
        hex_count_state_78(str_l, i, out) &&
        store_string(num@pre, str_l) *
        store_string(key, key_payload_78) *
        GlobalStrings_missing(LitMap, all_key_literals_78)
    */
    for (i = 0; i < n; i++) {
        int ch = num[i];
        char *found = strchr(key, ch) /*@ where str = key_payload_78 */;
        if (found != 0) {
            out = out + 1;
            /*@ Assert
                num == num@pre &&
                key == key_ptr_78(LitMap) &&
                n == string_length(str_l) &&
                0 <= i && i < n &&
                0 <= out && out <= i + 1 &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_78_pre_z(str_l) &&
                hex_count_safe_78(str_l) &&
                key_payload_safe_78 &&
                string_length(str_l) < INT_MAX &&
                hex_hit_step_78(str_l, i, out) &&
                hex_count_state_78(str_l, i + 1, out) &&
                store_string(num@pre, str_l) *
                store_string(key, key_payload_78) *
                GlobalStrings_missing(LitMap, all_key_literals_78) *
                data_at(&found, found)
            */
        } else {
            /*@ Assert
                num == num@pre &&
                key == key_ptr_78(LitMap) &&
                n == string_length(str_l) &&
                0 <= i && i < n &&
                0 <= out && out <= i &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_78_pre_z(str_l) &&
                hex_count_safe_78(str_l) &&
                key_payload_safe_78 &&
                string_length(str_l) < INT_MAX &&
                hex_miss_step_78(str_l, i, out) &&
                hex_count_state_78(str_l, i + 1, out) &&
                store_string(num@pre, str_l) *
                store_string(key, key_payload_78) *
                GlobalStrings_missing(LitMap, all_key_literals_78) *
                data_at(&found, found)
            */
        }
    }

    /*@ Assert
        num == num@pre &&
        key == key_ptr_78(LitMap) &&
        n == string_length(str_l) &&
        0 <= out && out <= n &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_78_pre_z(str_l) &&
        hex_count_safe_78(str_l) &&
        key_payload_safe_78 &&
        string_length(str_l) < INT_MAX &&
        hex_count_state_78(str_l, n, out) &&
        hex_final_78(str_l, out) &&
        problem_78_spec_z(str_l, out) &&
        store_string(num@pre, str_l) *
        store_string(key, key_payload_78) *
        GlobalStrings_missing(LitMap, all_key_literals_78) *
        data_at(&i, i)
    */
    return out;
}
