/*
Concatenate vector of strings into a single string
>>> concatenate({})
""
>>> concatenate({"a", "b", "c"})
"abc"
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_28_pre_z: list (list Z) -> Prop)
               (problem_28_spec_z: list (list Z) -> list Z -> Prop)
               (rows_well_formed_28: list (list Z) -> Z -> Prop)
               (row_payload_z_28: list Z -> list Z)
               (row_len_z_28: list Z -> Z)
               (total_prefix_state_28: list (list Z) -> Z -> Z -> Prop)
               (copy_prefix_state_28: list (list Z) -> Z -> Z -> list Z -> Prop)
               (concat_prefix_payload_28: list (list Z) -> Z -> list Z)
               (concat_prefix_len_28: list (list Z) -> Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import coins_28 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* concatenate(char** strings, int strings_size)
/*@ With rows
    Require
      0 <= strings_size && strings_size <= 100 &&
      rows_well_formed_28(rows, strings_size) &&
      (forall (p: Z), (0 <= p && p <= strings_size) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      problem_28_pre_z(rows) &&
      CharPtrArray2::full(strings, strings_size, rows)
    Ensure exists out_l,
      problem_28_spec_z(rows, out_l) &&
      CharPtrArray2::full(strings, strings_size, rows) *
      CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil)))
*/
{
    int total = 1;
    char* out = 0;
    int k = 0;
    int len0 = 0;
    int len = 0;
    char *cur = 0;
    /*@ Inv Assert
      0 <= i && i <= strings_size@pre &&
      0 <= strings_size@pre && strings_size@pre <= 100 &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      out == 0 &&
      k == 0 &&
      cur == cur &&
      0 <= len0 && len0 < INT_MAX &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_28(rows, strings_size@pre) &&
      (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      problem_28_pre_z(rows) &&
      total_prefix_state_28(rows, i, total) &&
      0 < total && total < INT_MAX &&
      CharPtrArray2::full(strings@pre, strings_size@pre, rows)
    */
    for (int i=0;i<strings_size;i++) {
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          out == 0 &&
          k == 0 &&
          cur == cur &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, i, total) &&
          valid_string(row_payload_z_28(Znth(i, rows, nil))) &&
          string_length(row_payload_z_28(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_28(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_28(Znth(i, rows, nil)))
        */
        cur = strings[i];
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          out == 0 &&
          k == 0 &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, i, total) &&
          valid_string(row_payload_z_28(Znth(i, rows, nil))) &&
          string_length(row_payload_z_28(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_28(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(cur, row_payload_z_28(Znth(i, rows, nil)))
        */
        len0 = (int)strlen(cur) /*@ where str = row_payload_z_28(Znth(i, rows, nil)) */;
        /*@ Assert
          exists row_ptr,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          out == 0 &&
          k == 0 &&
          len0 == row_len_z_28(Znth(i, rows, nil)) &&
          total + len0 < INT_MAX &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, i, total) &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        total += len0;
        /*@ Assert
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          out == 0 &&
          k == 0 &&
          cur == cur &&
          len0 == row_len_z_28(Znth(i, rows, nil)) &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, i + 1, total) &&
          0 < total && total < INT_MAX &&
          CharPtrArray2::full(strings@pre, strings_size@pre, rows)
        */
    }
    out = malloc_char_array(total);
    /*@ Inv Assert
      exists out_l,
      0 <= i && i <= strings_size@pre &&
      0 <= strings_size@pre && strings_size@pre <= 100 &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      cur == cur &&
      0 <= len0 && len0 < INT_MAX &&
      0 <= len && len < INT_MAX &&
      rows_well_formed_28(rows, strings_size@pre) &&
      (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      problem_28_pre_z(rows) &&
      total_prefix_state_28(rows, strings_size@pre, total) &&
      copy_prefix_state_28(rows, i, k, out_l) &&
      CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
      CharArray::full(out, k, out_l) *
      CharArray::undef_seg(out, k, total)
    */
    for (int i=0;i<strings_size;i++) {
        /*@ Assert
          exists row_ptr out_l,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == cur &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, strings_size@pre, total) &&
          copy_prefix_state_28(rows, i, k, out_l) &&
          valid_string(row_payload_z_28(Znth(i, rows, nil))) &&
          all_ascii(row_payload_z_28(Znth(i, rows, nil))) &&
          string_length(row_payload_z_28(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_28(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(row_ptr, row_payload_z_28(Znth(i, rows, nil))) *
          CharArray::full(out, k, out_l) *
          CharArray::undef_seg(out, k, total)
        */
        cur = strings[i];
        /*@ Assert
          exists row_ptr out_l,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, strings_size@pre, total) &&
          copy_prefix_state_28(rows, i, k, out_l) &&
          valid_string(row_payload_z_28(Znth(i, rows, nil))) &&
          all_ascii(row_payload_z_28(Znth(i, rows, nil))) &&
          string_length(row_payload_z_28(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_28(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(cur, row_payload_z_28(Znth(i, rows, nil))) *
          CharArray::full(out, k, out_l) *
          CharArray::undef_seg(out, k, total)
        */
        len = (int)strlen(cur) /*@ where str = row_payload_z_28(Znth(i, rows, nil)) */;
        /*@ Assert
          exists row_ptr out_l,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == row_ptr &&
          len == row_len_z_28(Znth(i, rows, nil)) &&
          k + len < total &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, strings_size@pre, total) &&
          copy_prefix_state_28(rows, i, k, out_l) &&
          all_ascii(row_payload_z_28(Znth(i, rows, nil))) &&
          Zlength(row_payload_z_28(Znth(i, rows, nil))) == len &&
          CharPtrArray2::missing_i(strings@pre, strings_size@pre, i, row_ptr, rows) *
          data_at(strings@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(cur, len, row_payload_z_28(Znth(i, rows, nil))) *
          CharArray::seg(cur, len, len + 1, cons(0, nil)) *
          CharArray::full(out, k, out_l) *
          CharArray::undef_full(out + k * sizeof(char), len) *
          CharArray::undef_seg(out, k + len, total)
        */
        memcpy(out + k, cur, len) /*@ where bytes = row_payload_z_28(Znth(i, rows, nil)) */;
        k += len;
        /*@ Assert
          exists out_l,
          0 <= i && i < strings_size@pre &&
          0 <= strings_size@pre && strings_size@pre <= 100 &&
          strings_size == strings_size@pre &&
          strings == strings@pre &&
          cur == cur &&
          0 <= len0 && len0 < INT_MAX &&
          0 <= len && len < INT_MAX &&
          rows_well_formed_28(rows, strings_size@pre) &&
          (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
            (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
          problem_28_pre_z(rows) &&
          total_prefix_state_28(rows, strings_size@pre, total) &&
          copy_prefix_state_28(rows, i + 1, k, out_l) &&
          CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
          CharArray::full(out, k, out_l) *
          CharArray::undef_seg(out, k, total)
        */
    }
    /*@ Assert
      exists out_l,
      k + 1 == total &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      rows_well_formed_28(rows, strings_size@pre) &&
      (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      cur == cur &&
      0 <= len0 && len0 < INT_MAX &&
      0 <= len && len < INT_MAX &&
      problem_28_pre_z(rows) &&
      copy_prefix_state_28(rows, strings_size@pre, k, out_l) &&
      CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
      CharArray::full(out, k, out_l) *
      CharArray::undef_seg(out, k, k + 1)
    */
    out[k] = '\0';
    /*@ Assert
      exists out_l,
      k + 1 == total &&
      strings_size == strings_size@pre &&
      strings == strings@pre &&
      rows_well_formed_28(rows, strings_size@pre) &&
      (forall (p: Z), (0 <= p && p <= strings_size@pre) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      cur == cur &&
      0 <= len0 && len0 < INT_MAX &&
      0 <= len && len < INT_MAX &&
      problem_28_pre_z(rows) &&
      copy_prefix_state_28(rows, strings_size@pre, k, out_l) &&
      problem_28_spec_z(rows, out_l) &&
      CharPtrArray2::full(strings@pre, strings_size@pre, rows) *
      CharArray::full(out, k + 1, app(out_l, cons(0, nil)))
    */
    return out;
}
