/*
Filter an input vector of strings only for ones that contain given substring
>>> filter_by_substring({}, "a")
{}
>>> filter_by_substring({"abc", "bacd", "cde", "vector"}, "a")
{"abc", "bacd", "vector"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_7_pre_z: list (list Z) -> Prop)
               (problem_7_spec_z: list (list Z) -> list Z -> list (list Z) -> Prop)
               (rows_well_formed_7: list (list Z) -> Z -> Prop)
               (row_payload_z_7: list Z -> list Z)
               (substring_match_z_7: list Z -> list Z -> Prop)
               (filter_substring_state_7: list (list Z) -> list Z -> Z -> list (list Z) -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_7 */

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

char **malloc_char_ptr_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && PtrArray::undef_full(__return, size)
*/;

StrArray *filter_by_substring(char** strings, int strings_size, char* substring)
/*@ With rows substring_l
    Require
      0 <= strings_size && strings_size <= 100 &&
      rows_well_formed_7(rows, strings_size) &&
      valid_string(substring_l) &&
      string_length(substring_l) < INT_MAX &&
      problem_7_pre_z(rows) &&
      CharPtrArray2::full(strings, strings_size, rows) *
      store_string(substring, substring_l)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 &&
      0 <= output_size && output_size <= strings_size &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      problem_7_spec_z(rows, substring_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      CharPtrArray2::full(strings, strings_size, rows) *
      store_string(substring, substring_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size)
*/
{
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(strings_size);
    char **data = out->data;
    int output_size = 0;
    char *cur = 0;
    char *hit = 0;
    /*@ Inv Assert
      exists output_rows output_ptrs,
      0 <= i && i <= strings_size@pre &&
      0 <= output_size && output_size <= i &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      substring == substring@pre &&
      out != 0 &&
      data != 0 &&
      cur == cur &&
      hit == hit &&
      rows_well_formed_7(rows, strings_size@pre) &&
      valid_string(substring_l) &&
      string_length(substring_l) < INT_MAX &&
      problem_7_pre_z(rows) &&
      filter_substring_state_7(rows, substring_l, i, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
      store_string(substring@pre, substring_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size@pre)
    */
    for (int i=0;i<strings_size;i++) {
        /*@ Assert
          exists row_ptr output_rows output_ptrs,
          0 <= i && i < strings_size@pre &&
          0 <= output_size && output_size <= i &&
          output_size == Zlength(output_rows) &&
          output_size == Zlength(output_ptrs) &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          substring == substring@pre &&
          out != 0 &&
          data != 0 &&
          cur == cur &&
          hit == hit &&
          rows_well_formed_7(rows, strings_size@pre) &&
          valid_string(substring_l) &&
          string_length(substring_l) < INT_MAX &&
          problem_7_pre_z(rows) &&
          filter_substring_state_7(rows, substring_l, i, output_rows) &&
          valid_string(row_payload_z_7(Znth(i, rows, nil))) &&
          string_length(row_payload_z_7(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_7(Znth(i, rows, nil))) + 1 &&
          data_at(&(out -> data), data) *
          data_at(&(out -> size), 0) *
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_7(Znth(i, rows, nil))) *
          store_string(substring@pre, substring_l) *
          PtrArray::seg(data, 0, output_size, output_ptrs) *
          PtrArray::undef_seg(data, output_size, strings_size@pre)
        */
        cur = strings[i];
        /*@ Assert
          exists row_ptr output_rows output_ptrs,
          0 <= i && i < strings_size@pre &&
          0 <= output_size && output_size <= i &&
          output_size == Zlength(output_rows) &&
          output_size == Zlength(output_ptrs) &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          substring == substring@pre &&
          cur == row_ptr &&
          out != 0 &&
          data != 0 &&
          hit == hit &&
          rows_well_formed_7(rows, strings_size@pre) &&
          valid_string(substring_l) &&
          string_length(substring_l) < INT_MAX &&
          problem_7_pre_z(rows) &&
          filter_substring_state_7(rows, substring_l, i, output_rows) &&
          valid_string(row_payload_z_7(Znth(i, rows, nil))) &&
          string_length(row_payload_z_7(Znth(i, rows, nil))) < INT_MAX &&
          data_at(&(out -> data), data) *
          data_at(&(out -> size), 0) *
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(cur, row_payload_z_7(Znth(i, rows, nil))) *
          store_string(substring@pre, substring_l) *
          PtrArray::seg(data, 0, output_size, output_ptrs) *
          PtrArray::undef_seg(data, output_size, strings_size@pre)
        */
        hit = strstr(cur, substring) /*@ where str1 = row_payload_z_7(Znth(i, rows, nil)), str2 = substring_l */;
        if (hit != 0) {
            /*@ Assert
              exists row_ptr output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings_size == strings_size@pre &&
              strings == strings@pre &&
              substring == substring@pre &&
              cur == row_ptr &&
              hit != 0 &&
              out != 0 &&
              data != 0 &&
              rows_well_formed_7(rows, strings_size@pre) &&
              valid_string(substring_l) &&
              string_length(substring_l) < INT_MAX &&
              problem_7_pre_z(rows) &&
              filter_substring_state_7(rows, substring_l, i, output_rows) &&
              substring_match_z_7(Znth(i, rows, nil), substring_l) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
              data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
              store_string(substring@pre, substring_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
            data[output_size] = cur;
            output_size = output_size + 1;
            /*@ Assert
              exists output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i + 1 &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings_size == strings_size@pre &&
              strings == strings@pre &&
              substring == substring@pre &&
              out != 0 &&
              data != 0 &&
              cur == cur &&
              hit != 0 &&
              rows_well_formed_7(rows, strings_size@pre) &&
              valid_string(substring_l) &&
              string_length(substring_l) < INT_MAX &&
              problem_7_pre_z(rows) &&
              filter_substring_state_7(rows, substring_l, i + 1, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
              store_string(substring@pre, substring_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
        } else {
            /*@ Assert
              exists row_ptr output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings_size == strings_size@pre &&
              strings == strings@pre &&
              substring == substring@pre &&
              cur == row_ptr &&
              hit == 0 &&
              out != 0 &&
              data != 0 &&
              rows_well_formed_7(rows, strings_size@pre) &&
              valid_string(substring_l) &&
              string_length(substring_l) < INT_MAX &&
              problem_7_pre_z(rows) &&
              filter_substring_state_7(rows, substring_l, i, output_rows) &&
              (! substring_match_z_7(Znth(i, rows, nil), substring_l)) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
              data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
              store_string(substring@pre, substring_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
            /*@ Assert
              exists output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i + 1 &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings_size == strings_size@pre &&
              strings == strings@pre &&
              substring == substring@pre &&
              out != 0 &&
              data != 0 &&
              cur == cur &&
              hit == 0 &&
              rows_well_formed_7(rows, strings_size@pre) &&
              valid_string(substring_l) &&
              string_length(substring_l) < INT_MAX &&
              problem_7_pre_z(rows) &&
              filter_substring_state_7(rows, substring_l, i + 1, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
              store_string(substring@pre, substring_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
        }
    }
    out->size = output_size;
    return out;
}
