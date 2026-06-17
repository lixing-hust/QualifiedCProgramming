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
               (scan_state_z: list (list Z) -> Z -> Z -> Z -> Z -> Prop)
               (rows_have_uniform_case_z: list (list Z) -> Prop)
               (invalid_char_seen_z: list (list Z) -> Z -> Z -> Prop)
               (mixed_case_seen_z: list (list Z) -> Z -> Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_95 */

int check_dict_case(const char** keys, int dict_size)
/*@ With rows
    Require
      0 <= dict_size && dict_size <= 100 &&
      rows_well_formed_z(rows, dict_size) &&
      problem_95_pre_z(rows) &&
      CharPtrArray2::full(keys, dict_size, rows)
    Ensure
      (__return == 0 || __return == 1) &&
      problem_95_spec_z(rows, __return) &&
      CharPtrArray2::full(keys, dict_size, rows)
*/
{
    int islower = 0, isupper = 0;
    if (dict_size == 0) {
        /*@ Assert
          dict_size == 0 &&
          keys == keys@pre &&
          islower == 0 &&
          isupper == 0 &&
          rows_well_formed_z(rows, dict_size@pre) &&
          problem_95_spec_z(rows, 0) &&
          CharPtrArray2::full(keys@pre, dict_size@pre, rows)
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
      scan_state_z(rows, k, 0, islower, isupper) &&
      CharPtrArray2::full(keys@pre, dict_size@pre, rows)
    */
    for (int k = 0; k < dict_size; k++) {
        /*@ Assert
          exists row_ptr,
          0 <= k && k < dict_size@pre &&
          0 < dict_size@pre && dict_size@pre <= 100 &&
          dict_size == dict_size@pre &&
          keys == keys@pre &&
          rows_well_formed_z(rows, dict_size@pre) &&
          problem_95_pre_z(rows) &&
          scan_state_z(rows, k, 0, islower, isupper) &&
          CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
          data_at(keys@pre + k * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        const char* key = keys[k];

        /*@ Assert
          exists row_ptr,
          0 <= k && k < dict_size@pre &&
          0 < dict_size@pre && dict_size@pre <= 100 &&
          dict_size == dict_size@pre &&
          keys == keys@pre &&
          key == row_ptr &&
          rows_well_formed_z(rows, dict_size@pre) &&
          problem_95_pre_z(rows) &&
          scan_state_z(rows, k, 0, islower, isupper) &&
          CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
          data_at(keys@pre + k * sizeof(char *), char *, row_ptr) *
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
          scan_state_z(rows, k, i, islower, isupper) &&
          CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
          data_at(keys@pre + k * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        for (int i = 0; key[i] != '\0'; i++) {
            if (key[i] < 65 || (key[i] > 90 && key[i] < 97) || key[i] > 122) {
                return 0;
            }
            if (key[i] >= 65 && key[i] <= 90) isupper = 1;
            if (key[i] >= 97 && key[i] <= 122) islower = 1;
            if (isupper + islower == 2) {
                return 0;
            }
        }
        /*@ Assert
          0 <= k && k < dict_size@pre &&
          0 < dict_size@pre && dict_size@pre <= 100 &&
          key == key &&
          k == k &&
          dict_size == dict_size@pre &&
          keys == keys@pre &&
          0 <= islower && islower <= 1 &&
          0 <= isupper && isupper <= 1 &&
          rows_well_formed_z(rows, dict_size@pre) &&
          problem_95_pre_z(rows) &&
          scan_state_z(rows, k + 1, 0, islower, isupper) &&
          CharPtrArray2::full(keys@pre, dict_size@pre, rows)
        */
    }
    return 1;
}
