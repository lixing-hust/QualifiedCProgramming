/*
Filter an input vector of strings, keeping exactly the strings that start with
the given prefix. Input order and duplicate occurrences are preserved.
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Import Coq Require Import SimpleC.EE.coins_29 */

/*@ Extern Coq
      (problem_29_pre_z : list (list Z) -> Prop)
      (problem_29_spec_z : list (list Z) -> list Z -> list (list Z) -> Prop)
      (row_payload_z_29 : list Z -> list Z)
      (row_well_formed_29 : list Z -> Prop)
      (rows_well_formed_29 : list (list Z) -> Z -> Prop)
      (prefix_hit_z_29 : list Z -> list Z -> Prop)
      (prefix_miss_z_29 : list Z -> list Z -> Prop)
      (filter_prefix_state_29 :
         list (list Z) -> list Z -> Z -> list (list Z) -> Prop)
 */

typedef struct {
    char **data;
    int size;
} StrArray;

StrArray *malloc_str_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/
;

char **malloc_char_ptr_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && PtrArray::undef_seg(__return, 0, size)
*/
;

StrArray *filter_by_prefix(char **strings, int strings_size, char *prefix)
/*@ With rows prefix_l strings_addr prefix_addr
    Require
      strings == strings_addr && prefix == prefix_addr &&
      0 <= strings_size && strings_size < INT_MAX &&
      rows_well_formed_29(rows, strings_size) &&
      problem_29_pre_z(rows) &&
      valid_string(prefix_l) &&
      string_length(prefix_l) < INT_MAX &&
      CharPtrArray2::full(strings, strings_size, rows) *
      store_string(prefix, prefix_l)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 && data != 0 &&
      0 <= output_size && output_size <= strings_size &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      problem_29_spec_z(rows, prefix_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      CharPtrArray2::full(strings_addr, strings_size, rows) *
      store_string(prefix_addr, prefix_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size)
*/
{
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(strings_size);
    char **data = out->data;
    int output_size = 0;
    int plen = strlen(prefix) /*@ where str = prefix_l */;
    char *cur = 0;
    int cmp = 0;
    int i;

    /*@ Inv Assert exists output_rows output_ptrs,
      0 <= i && i <= strings_size@pre &&
      0 <= output_size && output_size <= i &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      strings == strings_addr && prefix == prefix_addr &&
      strings_size == strings_size@pre &&
      plen == string_length(prefix_l) &&
      out != 0 && data != 0 && cur == cur && cmp == cmp &&
      rows_well_formed_29(rows, strings_size@pre) &&
      problem_29_pre_z(rows) && valid_string(prefix_l) &&
      string_length(prefix_l) < INT_MAX &&
      filter_prefix_state_29(rows, prefix_l, i, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      CharPtrArray2::full(strings_addr, strings_size@pre, rows) *
      store_string(prefix_addr, prefix_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size@pre)
    */
    for (i = 0; i < strings_size; i++) {
        /*@ Assert exists row_ptr output_rows output_ptrs,
          0 <= i && i < strings_size@pre &&
          0 <= output_size && output_size <= i &&
          output_size == Zlength(output_rows) &&
          output_size == Zlength(output_ptrs) &&
          strings == strings_addr && prefix == prefix_addr &&
          strings_size == strings_size@pre &&
          plen == string_length(prefix_l) &&
          out != 0 && data != 0 && cur == cur && cmp == cmp &&
          rows_well_formed_29(rows, strings_size@pre) &&
          row_well_formed_29(Znth(i, rows, nil)) &&
          problem_29_pre_z(rows) && valid_string(prefix_l) &&
          string_length(prefix_l) < INT_MAX &&
          filter_prefix_state_29(rows, prefix_l, i, output_rows) &&
          data_at(&(out -> data), data) *
          data_at(&(out -> size), 0) *
          CharPtrArray2::missing_i(strings_addr, strings_size@pre,
                                   i, row_ptr, rows) *
          data_at(strings_addr + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_29(Znth(i, rows, nil))) *
          store_string(prefix_addr, prefix_l) *
          PtrArray::seg(data, 0, output_size, output_ptrs) *
          PtrArray::undef_seg(data, output_size, strings_size@pre)
        */
        cur = strings[i];
        cmp = strncmp(cur, prefix, plen)
          /*@ where str1 = row_payload_z_29(Znth(i, rows, nil)),
                      str2 = prefix_l */;

        if (cmp == 0) {
            /*@ Assert exists row_ptr output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings == strings_addr && prefix == prefix_addr &&
              strings_size == strings_size@pre &&
              plen == string_length(prefix_l) &&
              out != 0 && data != 0 && cur == row_ptr && cmp == 0 &&
              rows_well_formed_29(rows, strings_size@pre) &&
              problem_29_pre_z(rows) && valid_string(prefix_l) &&
              string_length(prefix_l) < INT_MAX &&
              row_well_formed_29(Znth(i, rows, nil)) &&
              prefix_hit_z_29(row_payload_z_29(Znth(i, rows, nil)), prefix_l) &&
              filter_prefix_state_29(rows, prefix_l, i, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::missing_i(strings_addr, strings_size@pre,
                                       i, row_ptr, rows) *
              data_at(strings_addr + i * sizeof(char *), char *, row_ptr) *
              store_string(row_ptr, row_payload_z_29(Znth(i, rows, nil))) *
              store_string(prefix_addr, prefix_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
            data[output_size] = cur;
            output_size = output_size + 1;
        } else {
            /*@ Assert exists row_ptr output_rows output_ptrs,
              0 <= i && i < strings_size@pre &&
              0 <= output_size && output_size <= i &&
              output_size == Zlength(output_rows) &&
              output_size == Zlength(output_ptrs) &&
              strings == strings_addr && prefix == prefix_addr &&
              strings_size == strings_size@pre &&
              plen == string_length(prefix_l) &&
              out != 0 && data != 0 && cur == row_ptr && cmp != 0 &&
              rows_well_formed_29(rows, strings_size@pre) &&
              problem_29_pre_z(rows) && valid_string(prefix_l) &&
              string_length(prefix_l) < INT_MAX &&
              row_well_formed_29(Znth(i, rows, nil)) &&
              prefix_miss_z_29(row_payload_z_29(Znth(i, rows, nil)), prefix_l) &&
              filter_prefix_state_29(rows, prefix_l, i, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 0) *
              CharPtrArray2::missing_i(strings_addr, strings_size@pre,
                                       i, row_ptr, rows) *
              data_at(strings_addr + i * sizeof(char *), char *, row_ptr) *
              store_string(row_ptr, row_payload_z_29(Znth(i, rows, nil))) *
              store_string(prefix_addr, prefix_l) *
              PtrArray::seg(data, 0, output_size, output_ptrs) *
              PtrArray::undef_seg(data, output_size, strings_size@pre)
            */
        }
    }

    /*@ Assert exists output_rows output_ptrs,
      0 <= output_size && output_size <= strings_size@pre &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      strings == strings_addr && prefix == prefix_addr &&
      strings_size == strings_size@pre && out != 0 && data != 0 &&
      i == strings_size@pre && plen == string_length(prefix_l) &&
      cur == cur && cmp == cmp &&
      rows_well_formed_29(rows, strings_size@pre) &&
      problem_29_pre_z(rows) && valid_string(prefix_l) &&
      filter_prefix_state_29(rows, prefix_l, strings_size@pre, output_rows) &&
      problem_29_spec_z(rows, prefix_l, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      CharPtrArray2::full(strings_addr, strings_size@pre, rows) *
      store_string(prefix_addr, prefix_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size@pre)
    */
    out->size = output_size;
    return out;
}
