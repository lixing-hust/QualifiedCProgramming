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

#include "ptr_array2_def.h"

/*@ Extern Coq (problem_95_pre_z: list (list Z) -> Prop)
               (problem_95_spec_z: list (list Z) -> Z -> Prop)
               (rows_well_formed_z: list (list Z) -> Z -> Prop)
               (dict_case_state_z: Z -> Z -> list (list Z) -> Z -> Z -> Prop)
               (row_all_letters_z: list Z -> Prop)
               (row_all_lower_z: list Z -> Prop)
               (row_all_upper_z: list Z -> Prop)
               (rows_have_case_z: list (list Z) -> Prop)
               (processed_all_letters_z: Z -> Z -> list (list Z) -> Prop)
               (processed_has_lower_z: Z -> Z -> list (list Z) -> Prop)
               (processed_has_upper_z: Z -> Z -> list (list Z) -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_95 */

int check_dict_case(const char** keys, int dict_size)
/*@ With rows
    Require 0 <= dict_size && dict_size <= 100 &&
            rows_well_formed_z(rows, dict_size) &&
            problem_95_pre_z(rows) &&
            CharPtrArray2::full(keys, dict_size, rows)
    Ensure (__return == 0 || __return == 1) &&
           problem_95_spec_z(rows, __return) &&
           CharPtrArray2::full(keys, dict_size, rows)
*/
{
    int islower=0,isupper=0;
    if (dict_size==0) {
        /*@ Assert
            dict_size == 0 &&
            dict_size == dict_size@pre &&
            keys == keys@pre &&
            islower == 0 &&
            isupper == 0 &&
            rows_well_formed_z(rows, dict_size) &&
            problem_95_spec_z(rows, 0) &&
            CharPtrArray2::full(keys, dict_size, rows)
        */
        return 0;
    }
    /*@ Inv Assert
        0 <= k && k <= dict_size@pre &&
        0 < dict_size@pre && dict_size@pre <= 100 &&
        dict_size == dict_size@pre &&
        keys == keys@pre &&
        rows_well_formed_z(rows, dict_size@pre) &&
        problem_95_pre_z(rows) &&
        dict_case_state_z(k, 0, rows, islower, isupper) &&
        CharPtrArray2::full(keys@pre, dict_size@pre, rows)
    */
    for (int k=0;k<dict_size;k++)
    {
        /*@ Assert
            exists row_ptr,
            0 <= k && k < dict_size@pre &&
            0 < dict_size@pre && dict_size@pre <= 100 &&
            dict_size == dict_size@pre &&
            keys == keys@pre &&
            rows_well_formed_z(rows, dict_size@pre) &&
            problem_95_pre_z(rows) &&
            dict_case_state_z(k, 0, rows, islower, isupper) &&
            CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
            data_at(keys@pre + (k * sizeof(char *)), char *, row_ptr) *
            CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        const char* key=keys[k];

        /*@ Assert
            exists row_ptr,
            0 <= k && k < dict_size@pre &&
            0 < dict_size@pre && dict_size@pre <= 100 &&
            dict_size == dict_size@pre &&
            keys == keys@pre &&
            key == row_ptr &&
            rows_well_formed_z(rows, dict_size@pre) &&
            problem_95_pre_z(rows) &&
            dict_case_state_z(k, 0, rows, islower, isupper) &&
            CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
            data_at(keys@pre + (k * sizeof(char *)), char *, row_ptr) *
            CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        /*@ Inv Assert
            exists row_ptr,
            0 <= i && i < Zlength(Znth(k, rows, nil)) &&
            0 <= k && k < dict_size@pre &&
            0 < dict_size@pre && dict_size@pre <= 100 &&
            dict_size == dict_size@pre &&
            keys == keys@pre &&
            key == row_ptr &&
            rows_well_formed_z(rows, dict_size@pre) &&
            problem_95_pre_z(rows) &&
            dict_case_state_z(k, i, rows, islower, isupper) &&
            CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
            data_at(keys@pre + (k * sizeof(char *)), char *, row_ptr) *
            CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        for (int i=0;key[i]!='\0';i++)
        {
            if (key[i]<65 || (key[i]>90 && key[i]<97) || key[i]>122) {
                /*@ Assert
                    exists row_ptr,
                    0 <= k && k < dict_size@pre &&
                    0 <= i && i < Zlength(Znth(k, rows, nil)) - 1 &&
                    key == row_ptr &&
                    0 <= islower && islower <= 1 &&
                    0 <= isupper && isupper <= 1 &&
                    rows_well_formed_z(rows, dict_size@pre) &&
                    dict_case_state_z(k, i, rows, islower, isupper) &&
                    problem_95_spec_z(rows, 0) &&
                    CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
                    data_at(keys@pre + (k * sizeof(char *)), char *, row_ptr) *
                    CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
                */
                return 0;
            }
            if (key[i]>=65 && key[i]<=90) isupper=1;
            if (key[i]>=97 && key[i]<=122) islower=1;
            if (isupper+islower==2) {
                /*@ Assert
                    exists row_ptr,
                    0 <= k && k < dict_size@pre &&
                    0 <= i && i < Zlength(Znth(k, rows, nil)) - 1 &&
                    key == row_ptr &&
                    0 <= islower && islower <= 1 &&
                    0 <= isupper && isupper <= 1 &&
                    islower + isupper == 2 &&
                    rows_well_formed_z(rows, dict_size@pre) &&
                    processed_all_letters_z(k, i + 1, rows) &&
                    processed_has_lower_z(k, i + 1, rows) &&
                    processed_has_upper_z(k, i + 1, rows) &&
                    problem_95_spec_z(rows, 0) &&
                    CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
                    data_at(keys@pre + (k * sizeof(char *)), char *, row_ptr) *
                    CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
                */
                return 0;
            }
        }
        /*@ Assert
            exists row_ptr,
            0 <= k && k < dict_size@pre &&
            0 < dict_size@pre && dict_size@pre <= 100 &&
            dict_size == dict_size@pre &&
            keys == keys@pre &&
            key == row_ptr &&
            0 <= islower && islower <= 1 &&
            0 <= isupper && isupper <= 1 &&
            rows_well_formed_z(rows, dict_size@pre) &&
            problem_95_pre_z(rows) &&
            dict_case_state_z(k + 1, 0, rows, islower, isupper) &&
            CharPtrArray2::full(keys@pre, dict_size@pre, rows)
        */

    }
    /*@ Assert
        0 < dict_size@pre &&
        rows_well_formed_z(rows, dict_size@pre) &&
        dict_case_state_z(dict_size@pre, 0, rows, islower, isupper) &&
        rows_have_case_z(rows) &&
        problem_95_spec_z(rows, 1) &&
        CharPtrArray2::full(keys@pre, dict_size@pre, rows)
    */
    return 1;
}
