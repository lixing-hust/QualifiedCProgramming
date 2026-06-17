/*
Write a function that accepts two vectors of strings && returns the vector that has
total number of chars in the all strings of the vector less than the other vector.

if the two vectors have the same number of chars, return the first vector.

Examples
total_match({}, {}) -> {}
total_match({"hi", "admin"}, {"hI", "Hi"}) -> {"hI", "Hi"}
total_match({"hi", "admin"}, {"hi", "hi", "admin", "project"}) -> {"hi", "admin"}
total_match({"hi", "admin"}, {"hI", "hi", "hi"}) -> {"hI", "hi", "hi"}
total_match({"4"}, {"1", "2", "3", "4", "5"}) -> {"4"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_74_pre_z: list (list Z) -> list (list Z) -> Prop)
               (problem_74_spec_z: list (list Z) -> list (list Z) -> list (list Z) -> Prop)
               (rows_well_formed_74: list (list Z) -> Z -> Prop)
               (row_payload_z_74: list Z -> list Z)
               (row_len_z_74: list Z -> Z)
               (rows_total_len_z_74: list (list Z) -> Z)
               (total_prefix_state_74: list (list Z) -> Z -> Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_74 */

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray *malloc_str_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

StrArray *total_match(char** lst1, int lst1_size, char** lst2, int lst2_size)
/*@ With rows1 rows2
    Require
      0 <= lst1_size && lst1_size <= 100 &&
      0 <= lst2_size && lst2_size <= 100 &&
      rows_well_formed_74(rows1, lst1_size) &&
      rows_well_formed_74(rows2, lst2_size) &&
      problem_74_pre_z(rows1, rows2) &&
      CharPtrArray2::full(lst1, lst1_size, rows1) *
      CharPtrArray2::full(lst2, lst2_size, rows2)
    Ensure exists data output_rows output_size,
      __return != 0 &&
      0 <= output_size && output_size <= 100 &&
      problem_74_spec_z(rows1, rows2, output_rows) &&
      ((data == lst1 && output_size == lst1_size && output_rows == rows1) ||
       (data == lst2 && output_size == lst2_size && output_rows == rows2)) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      CharPtrArray2::full(lst1, lst1_size, rows1) *
      CharPtrArray2::full(lst2, lst2_size, rows2)
*/
{
    int num1 = 0;
    int num2 = 0;
    int len = 0;
    char *cur = 0;
    /*@ Inv Assert
      0 <= i && i <= lst1_size@pre &&
      lst1_size == lst1_size@pre &&
      lst2_size == lst2_size@pre &&
      lst1 == lst1@pre &&
      lst2 == lst2@pre &&
      num2 == 0 &&
      cur == cur &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_74(rows1, lst1_size@pre) &&
      rows_well_formed_74(rows2, lst2_size@pre) &&
      problem_74_pre_z(rows1, rows2) &&
      total_prefix_state_74(rows1, i, num1) &&
      0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
      0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
      CharPtrArray2::full(lst1@pre, lst1_size@pre, rows1) *
      CharPtrArray2::full(lst2@pre, lst2_size@pre, rows2)
    */
    for (int i=0;i<lst1_size;i++) {
        /*@ Assert
          exists row_ptr,
          0 <= i && i < lst1_size@pre &&
          lst1_size == lst1_size@pre &&
          lst2_size == lst2_size@pre &&
          lst1 == lst1@pre &&
          lst2 == lst2@pre &&
          num2 == 0 &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_74(rows1, lst1_size@pre) &&
          rows_well_formed_74(rows2, lst2_size@pre) &&
          problem_74_pre_z(rows1, rows2) &&
          total_prefix_state_74(rows1, i, num1) &&
          valid_string(row_payload_z_74(Znth(i, rows1, nil))) &&
          string_length(row_payload_z_74(Znth(i, rows1, nil))) < INT_MAX &&
          Zlength(Znth(i, rows1, nil)) == string_length(row_payload_z_74(Znth(i, rows1, nil))) + 1 &&
          0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
          0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
          CharPtrArray2::missing_i(lst1@pre, lst1_size@pre, i, row_ptr, rows1) *
          data_at(lst1@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_74(Znth(i, rows1, nil))) *
          CharPtrArray2::full(lst2@pre, lst2_size@pre, rows2)
        */
        cur = lst1[i];
        len = (int)strlen(cur) /*@ where str = row_payload_z_74(Znth(i, rows1, nil)) */;
        num1 += len;
        /*@ Assert
          0 <= i && i < lst1_size@pre &&
          lst1_size == lst1_size@pre &&
          lst2_size == lst2_size@pre &&
          lst1 == lst1@pre &&
          lst2 == lst2@pre &&
          num2 == 0 &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_74(rows1, lst1_size@pre) &&
          rows_well_formed_74(rows2, lst2_size@pre) &&
          problem_74_pre_z(rows1, rows2) &&
          total_prefix_state_74(rows1, i + 1, num1) &&
          0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
          0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
          CharPtrArray2::full(lst1@pre, lst1_size@pre, rows1) *
          CharPtrArray2::full(lst2@pre, lst2_size@pre, rows2)
        */
    }
    /*@ Inv Assert
      0 <= i && i <= lst2_size@pre &&
      lst1_size == lst1_size@pre &&
      lst2_size == lst2_size@pre &&
      lst1 == lst1@pre &&
      lst2 == lst2@pre &&
      num1 == rows_total_len_z_74(rows1) &&
      cur == cur &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_74(rows1, lst1_size@pre) &&
      rows_well_formed_74(rows2, lst2_size@pre) &&
      problem_74_pre_z(rows1, rows2) &&
      total_prefix_state_74(rows2, i, num2) &&
      0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
      0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
      CharPtrArray2::full(lst1@pre, lst1_size@pre, rows1) *
      CharPtrArray2::full(lst2@pre, lst2_size@pre, rows2)
    */
    for (int i=0;i<lst2_size;i++) {
        /*@ Assert
          exists row_ptr,
          0 <= i && i < lst2_size@pre &&
          lst1_size == lst1_size@pre &&
          lst2_size == lst2_size@pre &&
          lst1 == lst1@pre &&
          lst2 == lst2@pre &&
          num1 == rows_total_len_z_74(rows1) &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_74(rows1, lst1_size@pre) &&
          rows_well_formed_74(rows2, lst2_size@pre) &&
          problem_74_pre_z(rows1, rows2) &&
          total_prefix_state_74(rows2, i, num2) &&
          valid_string(row_payload_z_74(Znth(i, rows2, nil))) &&
          string_length(row_payload_z_74(Znth(i, rows2, nil))) < INT_MAX &&
          Zlength(Znth(i, rows2, nil)) == string_length(row_payload_z_74(Znth(i, rows2, nil))) + 1 &&
          0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
          0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
          CharPtrArray2::full(lst1@pre, lst1_size@pre, rows1) *
          CharPtrArray2::missing_i(lst2@pre, lst2_size@pre, i, row_ptr, rows2) *
          data_at(lst2@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_74(Znth(i, rows2, nil)))
        */
        cur = lst2[i];
        len = (int)strlen(cur) /*@ where str = row_payload_z_74(Znth(i, rows2, nil)) */;
        num2 += len;
        /*@ Assert
          0 <= i && i < lst2_size@pre &&
          lst1_size == lst1_size@pre &&
          lst2_size == lst2_size@pre &&
          lst1 == lst1@pre &&
          lst2 == lst2@pre &&
          num1 == rows_total_len_z_74(rows1) &&
          cur == cur &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_74(rows1, lst1_size@pre) &&
          rows_well_formed_74(rows2, lst2_size@pre) &&
          problem_74_pre_z(rows1, rows2) &&
          total_prefix_state_74(rows2, i + 1, num2) &&
          0 <= rows_total_len_z_74(rows1) && rows_total_len_z_74(rows1) <= INT_MAX &&
          0 <= rows_total_len_z_74(rows2) && rows_total_len_z_74(rows2) <= INT_MAX &&
          CharPtrArray2::full(lst1@pre, lst1_size@pre, rows1) *
          CharPtrArray2::full(lst2@pre, lst2_size@pre, rows2)
        */
    }
    StrArray *out = malloc_str_array_struct();
    if (num1 > num2) {
        out->data = lst2;
        out->size = lst2_size;
        return out;
    }
    out->data = lst1;
    out->size = lst1_size;
    return out;
}
