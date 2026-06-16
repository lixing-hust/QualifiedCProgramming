/*
Given a map, return true if all keys are strings in lower
case || all keys are strings in upper case, else return false.
The function should return false is the given map is empty.
Examples:
check_map_case({{"a","apple"}, {"b","banana"}}) should return true.
check_map_case({{"a","apple"}, {"A","banana"}, {"B","banana"}}) should return false.
check_map_case({{"a","apple"}, {"8","banana"}, {"a","apple"}}) should return false.
check_map_case({{"Name","John"}, {"Age","36"}, {"City","Houston"}}) should return false.
check_map_case({{"STATE","NC"}, {"ZIP","12345"} }) should return true.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "ptr_array_def.h"

/*@ Extern Coq (problem_95_pre_z: list (list Z) -> Prop)
               (problem_95_spec_z: list (list Z) -> Z -> Prop)
               (string_lengths_z: list (list Z) -> list Z -> Prop)
               (string_rows_full: list Z -> list Z -> list (list Z) -> Assertion)
               (dict_case_prefix_z: Z -> list (list Z) -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_95 */

int strlen(char *s)
/*@ With l len
    Require
        0 <= len &&
        Zlength(l) == len &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        __return == len &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
;

int check_dict_case(char **keys, int dict_size)
/*@ With key_ls lens ptrs
    Require
        0 <= dict_size && dict_size < INT_MAX &&
        Zlength(key_ls) == dict_size &&
        Zlength(lens) == dict_size &&
        Zlength(ptrs) == dict_size &&
        string_lengths_z(key_ls, lens) &&
        problem_95_pre_z(key_ls) &&
        PtrArray::full(keys, dict_size, ptrs) *
        string_rows_full(ptrs, lens, key_ls)
    Ensure
        (__return == 0 || __return == 1) &&
        problem_95_spec_z(key_ls, __return) &&
        PtrArray::full(keys, dict_size, ptrs) *
        string_rows_full(ptrs, lens, key_ls)
*/
{
    int islower = 0;
    int isupper = 0;
    int k;
    int i;
    int key_len;
    char *key;

    i = 0;
    key_len = 0;
    key = 0;
    if (dict_size == 0) return 0;

    /*@ Inv Assert
        0 <= k && k <= dict_size &&
        dict_size > 0 &&
        0 <= islower && islower <= 1 &&
        0 <= isupper && isupper <= 1 &&
        islower + isupper <= 1 &&
        i == i &&
        key_len == key_len &&
        key == key &&
        Zlength(key_ls) == dict_size &&
        Zlength(lens) == dict_size &&
        Zlength(ptrs) == dict_size &&
        string_lengths_z(key_ls, lens) &&
        problem_95_pre_z(key_ls) &&
        dict_case_prefix_z(k, key_ls, islower, isupper) &&
        PtrArray::full(keys, dict_size, ptrs) *
        string_rows_full(ptrs, lens, key_ls)
    */
    for (k = 0; k < dict_size; k++) {
        key = keys[k];
        key_len = strlen(key) /*@ where l = key_ls[k], len = lens[k] */;

        /*@ Inv Assert
            0 <= k && k < dict_size &&
            0 <= i && i <= key_len &&
            key == ptrs[k] &&
            key_len == lens[k] &&
            dict_size > 0 &&
            0 <= islower && islower <= 1 &&
            0 <= isupper && isupper <= 1 &&
            islower + isupper <= 1 &&
            Zlength(key_ls) == dict_size &&
            Zlength(lens) == dict_size &&
            Zlength(ptrs) == dict_size &&
            string_lengths_z(key_ls, lens) &&
            problem_95_pre_z(key_ls) &&
            dict_case_prefix_z(k, key_ls, islower, isupper) &&
            PtrArray::full(keys, dict_size, ptrs) *
            string_rows_full(ptrs, lens, key_ls)
        */
        for (i = 0; i < key_len; i++) {
            if (key[i] < 65 || (key[i] > 90 && key[i] < 97) || key[i] > 122) return 0;
            if (key[i] >= 65 && key[i] <= 90) isupper = 1;
            if (key[i] >= 97 && key[i] <= 122) islower = 1;
            if (isupper + islower == 2) return 0;
        }
    }
    return 1;
}
