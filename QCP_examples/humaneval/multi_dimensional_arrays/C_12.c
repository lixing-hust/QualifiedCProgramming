/*
Out of vector of strings, return the longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input vector is empty.
>>> longest({})

>>> longest({"a", "b", "c"})
"a"
>>> longest({"a", "bb", "ccc"})
"ccc"
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_12_pre_z: list (list Z) -> Prop)
               (problem_12_spec_none_z: list (list Z) -> Prop)
               (problem_12_spec_some_z: list (list Z) -> Z -> Prop)
               (rows_well_formed_12: list (list Z) -> Z -> Prop)
               (row_payload_z_12: list Z -> list Z)
               (row_len_z_12: list Z -> Z)
               (longest_prefix_z_12: list (list Z) -> Z -> Z -> Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_12 */

const char* longest(const char** strings, int strings_size)
/*@ With rows
    Require
      0 <= strings_size && strings_size <= 100 &&
      rows_well_formed_12(rows, strings_size) &&
      problem_12_pre_z(rows) &&
      CharPtrArray2::full(strings, strings_size, rows)
    Ensure
      (strings_size == 0 &&
       __return == 0 &&
       problem_12_spec_none_z(rows) &&
       CharPtrArray2::full(strings, strings_size, rows)) ||
      (exists best_idx row_ptr,
       0 < strings_size &&
       0 <= best_idx && best_idx < strings_size &&
       __return == row_ptr &&
       problem_12_spec_some_z(rows, best_idx) &&
       CharPtrArray2::missing_i(strings, strings_size, best_idx, row_ptr, rows) *
       data_at(strings + best_idx * sizeof(char *), char *, row_ptr) *
       CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil)))
*/
{
    if (strings_size == 0) {
        return 0;
    }
    int best = -1;
    int best_idx = -1;
    int len = 0;
    const char* cur = 0;
    /*@ Inv Assert
      0 <= i && i <= strings_size@pre &&
      0 < strings_size@pre && strings_size@pre <= 100 &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      cur == cur &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_12(rows, strings_size@pre) &&
      problem_12_pre_z(rows) &&
      longest_prefix_z_12(rows, i, best_idx, best) &&
      CharPtrArray2::full(strings@pre, strings_size@pre, rows)
    */
    for (int i=0;i<strings_size;i++)
    {
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 < strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_12(rows, strings_size@pre) &&
          problem_12_pre_z(rows) &&
          longest_prefix_z_12(rows, i, best_idx, best) &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        cur = strings[i];
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 < strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_12(rows, strings_size@pre) &&
          problem_12_pre_z(rows) &&
          longest_prefix_z_12(rows, i, best_idx, best) &&
          valid_string(row_payload_z_12(Znth(i, rows, nil))) &&
          string_length(row_payload_z_12(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_12(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(cur, row_payload_z_12(Znth(i, rows, nil)))
        */
        len = (int)strlen(cur) /*@ where str = row_payload_z_12(Znth(i, rows, nil)) */;
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 < strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          len == row_len_z_12(Znth(i, rows, nil)) &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_12(rows, strings_size@pre) &&
          problem_12_pre_z(rows) &&
          longest_prefix_z_12(rows, i, best_idx, best) &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        if (len > best) {
            best = len;
            best_idx = i;
        }
        /*@ Assert
          0 <= i && i < strings_size@pre &&
          0 < strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_12(rows, strings_size@pre) &&
          problem_12_pre_z(rows) &&
          longest_prefix_z_12(rows, i + 1, best_idx, best) &&
          CharPtrArray2::full(strings@pre, strings_size@pre, rows)
        */
    }
    /*@ Assert
      exists row_ptr,
      0 < strings_size@pre &&
      0 <= best_idx && best_idx < strings_size@pre &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      cur == cur &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_12(rows, strings_size@pre) &&
      problem_12_pre_z(rows) &&
      longest_prefix_z_12(rows, strings_size@pre, best_idx, best) &&
      problem_12_spec_some_z(rows, best_idx) &&
      CharPtrArray2::missing_i(strings@pre, strings_size@pre, best_idx, row_ptr, rows) *
      data_at(strings@pre + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil))
    */
    return strings[best_idx];
}
