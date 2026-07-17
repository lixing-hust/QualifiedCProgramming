/*
Given a map, return true if all keys are strings in lower
case || all keys are strings in upper case, else return false.
The function should return false is the given map is empty.
*/

#include "ptr_array2_def.h"

/*@ Extern Coq
      (problem_95_pre_z : list (list Z) -> Prop)
      (problem_95_spec_z : list (list Z) -> Z -> Prop)
      (rows_well_formed_z_95 : list (list Z) -> Z -> Prop)
      (dict_case_state_z_95 : Z -> Z -> list (list Z) -> Z -> Z -> Prop)
      (Znth : {A} -> Z -> list A -> A -> A)
      (Zlength : {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_95 */

int check_dict_case(const char **keys, int dict_size)
/*@ With rows
    Require
      0 <= dict_size && dict_size <= 100 &&
      rows_well_formed_z_95(rows, dict_size) &&
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
        return 0;
    }

    /*@ Inv Assert
      0 <= k && k <= dict_size@pre &&
      0 < dict_size@pre && dict_size@pre <= 100 &&
      dict_size == dict_size@pre && keys == keys@pre &&
      rows_well_formed_z_95(rows, dict_size@pre) &&
      problem_95_pre_z(rows) &&
      dict_case_state_z_95(k, 0, rows, islower, isupper) &&
      CharPtrArray2::full(keys@pre, dict_size@pre, rows)
    */
    for (int k = 0; k < dict_size; k++) {
        /*@ Assert
          exists row_ptr,
          0 <= k && k < dict_size@pre &&
          0 < dict_size@pre && dict_size@pre <= 100 &&
          dict_size == dict_size@pre && keys == keys@pre &&
          rows_well_formed_z_95(rows, dict_size@pre) &&
          problem_95_pre_z(rows) &&
          dict_case_state_z_95(k, 0, rows, islower, isupper) &&
          CharPtrArray2::missing_i(keys@pre, dict_size@pre, k, row_ptr, rows) *
          data_at(keys@pre + k * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(k, rows, nil)), Znth(k, rows, nil))
        */
        const char *key = keys[k];

        /*@ Inv Assert
          exists row_ptr,
          0 <= i && i < Zlength(Znth(k, rows, nil)) &&
          0 <= k && k < dict_size@pre &&
          0 < dict_size@pre && dict_size@pre <= 100 &&
          dict_size == dict_size@pre && keys == keys@pre &&
          key == row_ptr &&
          rows_well_formed_z_95(rows, dict_size@pre) &&
          problem_95_pre_z(rows) &&
          dict_case_state_z_95(k, i, rows, islower, isupper) &&
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
    }

    return 1;
}
