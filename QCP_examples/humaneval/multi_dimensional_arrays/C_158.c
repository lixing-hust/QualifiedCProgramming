/*
Write a function that accepts a vector of strings.
The vector contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max({"name", "of", 'string"}) == 'string"
find_max({"name", "enam", "game"}) == "enam"
find_max({"aaaaaaa", "bb" ,"cc"}) == "aaaaaaa"
*/
#include "ptr_array2_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_158_pre_z: list (list Z) -> Prop)
               (problem_158_spec_z: list (list Z) -> Z -> Prop)
               (rows_well_formed_158: list (list Z) -> Z -> Prop)
               (row_payload_z_158: list Z -> list Z)
               (row_unique_count_z_158: list Z -> Z)
               (count_scan_state_158: list Z -> Z -> list Z -> Z -> Prop)
               (best_prefix_state_158: list (list Z) -> Z -> Z -> Z -> Prop)
               (reset_prefix_state_158: Z -> list Z -> Prop)
               (strcmp_negative_158: list Z -> list Z -> Z -> Prop)
               (char_ptr_array2_missing_two_158:
                  Z -> Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (zeros: Z -> list Z)
*/
/*@ Import Coq Require Import coins_158 */

char* find_max(char** words, int words_size)
/*@ With rows
    Require
      0 < words_size && words_size <= 100 &&
      rows_well_formed_158(rows, words_size) &&
      problem_158_pre_z(rows) &&
      CharPtrArray2::full(words, words_size, rows)
    Ensure exists best_idx row_ptr,
      0 <= best_idx && best_idx < words_size &&
      __return == row_ptr &&
      problem_158_spec_z(rows, best_idx) &&
      CharPtrArray2::missing_i(words, words_size, best_idx, row_ptr, rows) *
      data_at(words + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil))
*/
{
    char* max;
    char* cur;
    int seen[128];
    int maxu;
    int unique;
    int cmp;
    int best_idx;
    int i;
    int j;
    int k;
    int len;
    int ch;

    max = words[0];
    maxu = 0;
    unique = 0;
    cmp = 0;
    best_idx = 0;
    cur = 0;
    i = 0;
    j = 0;
    len = 0;
    ch = 0;

    k = 0;
    /*@ Inv Assert
      0 <= k && k <= 128 &&
      words_size == words_size@pre &&
      words == words@pre &&
      max == max &&
      cur == cur &&
      i == i &&
      j == 0 &&
      k == k &&
      len == 0 &&
      ch == 0 &&
      cmp == cmp &&
      maxu == 0 &&
      unique == 0 &&
      best_idx == 0 &&
      0 < words_size@pre && words_size@pre <= 100 &&
      rows_well_formed_158(rows, words_size@pre) &&
      problem_158_pre_z(rows) &&
      CharPtrArray2::full(words@pre, words_size@pre, rows) *
      IntArray::seg(seen, 0, k, zeros(k)) *
      IntArray::undef_seg(seen, k, 128)
    */
    while (k < 128) {
        seen[k] = 0;
        k = k + 1;
    }

    i = 0;
    /*@ Inv Assert
      exists seen_l,
      0 <= i && i <= words_size@pre &&
      0 < words_size@pre && words_size@pre <= 100 &&
      words_size == words_size@pre &&
      words == words@pre &&
      max == max &&
      cur == cur &&
      k == k &&
      j == j &&
      cmp == cmp &&
      len == len &&
      ch == ch &&
      0 <= best_idx && best_idx < words_size@pre &&
      0 <= maxu && maxu <= 128 &&
      0 <= unique && unique <= 128 &&
      rows_well_formed_158(rows, words_size@pre) &&
      problem_158_pre_z(rows) &&
      best_prefix_state_158(rows, i, best_idx, maxu) &&
      Zlength(seen_l) == 128 &&
      CharPtrArray2::full(words@pre, words_size@pre, rows) *
      IntArray::full(seen, 128, seen_l)
    */
    while (i < words_size) {
        /*@ Assert
          exists row_ptr seen_l,
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == cur &&
          k == k &&
          j == j &&
          cmp == cmp &&
          len == len &&
          ch == ch &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_prefix_state_158(rows, i, best_idx, maxu) &&
          Zlength(seen_l) == 128 &&
          CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
          data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
          IntArray::full(seen, 128, seen_l)
        */
        k = 0;
        /*@ Inv Assert
          exists row_ptr seen_l,
          0 <= k && k <= 128 &&
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == cur &&
          j == j &&
          k == k &&
          cmp == cmp &&
          len == len &&
          ch == ch &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_prefix_state_158(rows, i, best_idx, maxu) &&
          Zlength(seen_l) == 128 &&
          reset_prefix_state_158(k, seen_l) &&
          CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
          data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
          IntArray::full(seen, 128, seen_l)
        */
        while (k < 128) {
            seen[k] = 0;
            k = k + 1;
        }

        /*@ Assert
          exists row_ptr,
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == cur &&
          j == j &&
          k == k &&
          cmp == cmp &&
          len == len &&
          ch == ch &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_prefix_state_158(rows, i, best_idx, maxu) &&
          IntArray::full(seen, 128, zeros(128)) *
          CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
          data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil))
        */
        cur = words[i];

        /*@ Assert
          exists row_ptr,
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == row_ptr &&
          k == k &&
          j == j &&
          cmp == cmp &&
          len == len &&
          ch == ch &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_prefix_state_158(rows, i, best_idx, maxu) &&
          valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
          string_length(row_payload_z_158(Znth(i, rows, nil))) < INT_MAX &&
          Zlength(Znth(i, rows, nil)) == string_length(row_payload_z_158(Znth(i, rows, nil))) + 1 &&
          CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
          data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
          store_string(cur, row_payload_z_158(Znth(i, rows, nil))) *
          IntArray::full(seen, 128, zeros(128))
        */
        len = (int)strlen(cur) /*@ where str = row_payload_z_158(Znth(i, rows, nil)) */;
        unique = 0;
        j = 0;
        ch = 0;
        /*@ Inv Assert
          exists row_ptr seen_l,
          0 <= j && j <= len &&
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == row_ptr &&
          k == k &&
          cmp == cmp &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          len == string_length(row_payload_z_158(Znth(i, rows, nil))) &&
          Zlength(Znth(i, rows, nil)) == len + 1 &&
          valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
          0 <= ch && ch <= 127 &&
          Zlength(seen_l) == 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_prefix_state_158(rows, i, best_idx, maxu) &&
          count_scan_state_158(Znth(i, rows, nil), j, seen_l, unique) &&
          CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
          data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
          CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
          IntArray::full(seen, 128, seen_l)
        */
        while (j < len) {
            ch = cur[j];
            /*@ Assert
	              exists row_ptr seen_l,
	              0 <= j && j < len &&
	              0 <= i && i < words_size@pre &&
	              0 < words_size@pre && words_size@pre <= 100 &&
	              words_size == words_size@pre &&
              words == words@pre &&
              max == max &&
              cur == row_ptr &&
              k == k &&
	              cmp == cmp &&
	              0 <= ch && ch < 128 &&
	              ch == Znth(j, Znth(i, rows, nil), 0) &&
	              0 <= best_idx && best_idx < words_size@pre &&
              0 <= maxu && maxu <= 128 &&
              0 <= unique && unique <= 128 &&
              len == string_length(row_payload_z_158(Znth(i, rows, nil))) &&
              Zlength(Znth(i, rows, nil)) == len + 1 &&
              valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
              Zlength(seen_l) == 128 &&
              rows_well_formed_158(rows, words_size@pre) &&
              problem_158_pre_z(rows) &&
              best_prefix_state_158(rows, i, best_idx, maxu) &&
              count_scan_state_158(Znth(i, rows, nil), j, seen_l, unique) &&
              CharPtrArray2::missing_i(words@pre, words_size@pre, i, row_ptr, rows) *
              data_at(words@pre + i * sizeof(char *), char *, row_ptr) *
              CharArray::full(row_ptr, Zlength(Znth(i, rows, nil)), Znth(i, rows, nil)) *
              IntArray::full(seen, 128, seen_l)
            */
            if (seen[ch] == 0) {
                seen[ch] = 1;
                unique = unique + 1;
            }
            j = j + 1;
        }

        if (unique > maxu) {
            max = cur;
            maxu = unique;
            best_idx = i;
        } else {
            if (unique == maxu && i != best_idx) {
                /*@ Assert
                  exists row_ptr best_ptr seen_l,
                  0 <= i && i < words_size@pre &&
                  0 < words_size@pre && words_size@pre <= 100 &&
                  0 <= best_idx && best_idx < words_size@pre &&
                  i != best_idx &&
                  words_size == words_size@pre &&
                  words == words@pre &&
                  cur == row_ptr &&
                  max == max &&
                  k == k &&
                  j == j &&
                  cmp == cmp &&
                  unique == row_unique_count_z_158(Znth(i, rows, nil)) &&
                  unique == maxu &&
                  0 <= maxu && maxu <= 128 &&
                  0 <= unique && unique <= 128 &&
                  rows_well_formed_158(rows, words_size@pre) &&
                  problem_158_pre_z(rows) &&
                  best_prefix_state_158(rows, i, best_idx, maxu) &&
                  valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
                  valid_string(row_payload_z_158(Znth(best_idx, rows, nil))) &&
                  string_length(row_payload_z_158(Znth(i, rows, nil))) < INT_MAX &&
                  string_length(row_payload_z_158(Znth(best_idx, rows, nil))) < INT_MAX &&
                  Zlength(seen_l) == 128 &&
	                  char_ptr_array2_missing_two_158(words@pre, words_size@pre, i, row_ptr, best_idx, best_ptr, rows) *
	                  store_string(row_ptr, row_payload_z_158(Znth(i, rows, nil))) *
	                  data_at(words@pre + best_idx * sizeof(char *), char *, best_ptr) *
	                  store_string(best_ptr, row_payload_z_158(Znth(best_idx, rows, nil))) *
	                  data_at(&len, int, len) *
	                  data_at(&ch, int, ch) *
	                  IntArray::full(seen, 128, seen_l)
	                */
                max = words[best_idx];
                /*@ Assert
                  exists row_ptr best_ptr seen_l,
                  0 <= i && i < words_size@pre &&
                  0 < words_size@pre && words_size@pre <= 100 &&
                  0 <= best_idx && best_idx < words_size@pre &&
                  i != best_idx &&
                  words_size == words_size@pre &&
                  words == words@pre &&
                  cur == row_ptr &&
                  max == best_ptr &&
                  k == k &&
                  j == j &&
                  cmp == cmp &&
                  unique == row_unique_count_z_158(Znth(i, rows, nil)) &&
                  unique == maxu &&
                  0 <= maxu && maxu <= 128 &&
                  0 <= unique && unique <= 128 &&
                  rows_well_formed_158(rows, words_size@pre) &&
                  problem_158_pre_z(rows) &&
                  best_prefix_state_158(rows, i, best_idx, maxu) &&
                  valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
                  valid_string(row_payload_z_158(Znth(best_idx, rows, nil))) &&
                  string_length(row_payload_z_158(Znth(i, rows, nil))) < INT_MAX &&
	                  string_length(row_payload_z_158(Znth(best_idx, rows, nil))) < INT_MAX &&
	                  Zlength(seen_l) == 128 &&
		                  char_ptr_array2_missing_two_158(words@pre, words_size@pre, i, row_ptr, best_idx, best_ptr, rows) *
		                  store_string(row_ptr, row_payload_z_158(Znth(i, rows, nil))) *
		                  data_at(words@pre + best_idx * sizeof(char *), char *, best_ptr) *
		                  store_string(best_ptr, row_payload_z_158(Znth(best_idx, rows, nil))) *
		                  data_at(&len, int, len) *
		                  data_at(&ch, int, ch) *
	                  IntArray::full(seen, 128, seen_l)
	                */
                cmp = strcmp(cur, max)
                  /*@ where str1 = row_payload_z_158(Znth(i, rows, nil)),
                            str2 = row_payload_z_158(Znth(best_idx, rows, nil)) */;
                /*@ Assert
                  exists row_ptr best_ptr seen_l,
                  0 <= i && i < words_size@pre &&
                  0 < words_size@pre && words_size@pre <= 100 &&
                  0 <= best_idx && best_idx < words_size@pre &&
                  i != best_idx &&
                  words_size == words_size@pre &&
                  words == words@pre &&
                  cur == row_ptr &&
                  max == best_ptr &&
                  k == k &&
                  j == j &&
                  unique == row_unique_count_z_158(Znth(i, rows, nil)) &&
                  unique == maxu &&
                  0 <= maxu && maxu <= 128 &&
                  0 <= unique && unique <= 128 &&
                  rows_well_formed_158(rows, words_size@pre) &&
                  problem_158_pre_z(rows) &&
                  best_prefix_state_158(rows, i, best_idx, maxu) &&
                  valid_string(row_payload_z_158(Znth(i, rows, nil))) &&
                  valid_string(row_payload_z_158(Znth(best_idx, rows, nil))) &&
                  string_length(row_payload_z_158(Znth(i, rows, nil))) < INT_MAX &&
                  string_length(row_payload_z_158(Znth(best_idx, rows, nil))) < INT_MAX &&
                  strcmp_result(row_payload_z_158(Znth(i, rows, nil)),
                                row_payload_z_158(Znth(best_idx, rows, nil)),
                                cmp) &&
                  Zlength(seen_l) == 128 &&
                  char_ptr_array2_missing_two_158(words@pre, words_size@pre, i, row_ptr, best_idx, best_ptr, rows) *
                  store_string(row_ptr, row_payload_z_158(Znth(i, rows, nil))) *
                  data_at(words@pre + best_idx * sizeof(char *), char *, best_ptr) *
                  store_string(best_ptr, row_payload_z_158(Znth(best_idx, rows, nil))) *
                  data_at(&len, int, len) *
                  data_at(&ch, int, ch) *
                  IntArray::full(seen, 128, seen_l)
                */
                if (cmp < 0) {
                    max = cur;
                    best_idx = i;
                }
            }
        }
        /*@ Assert
          exists seen_l,
          0 <= i && i < words_size@pre &&
          0 < words_size@pre && words_size@pre <= 100 &&
          words_size == words_size@pre &&
          words == words@pre &&
          max == max &&
          cur == cur &&
          j == j &&
          cmp == cmp &&
          len == len &&
          ch == ch &&
          0 <= best_idx && best_idx < words_size@pre &&
          0 <= maxu && maxu <= 128 &&
          0 <= unique && unique <= 128 &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
	          best_prefix_state_158(rows, i + 1, best_idx, maxu) &&
	          Zlength(seen_l) == 128 &&
	          CharPtrArray2::full(words@pre, words_size@pre, rows) *
	          data_at(&k, int, k) *
	          IntArray::full(seen, 128, seen_l)
	        */
        i = i + 1;
    }
    /*@ Assert
      exists row_ptr seen_l,
      0 <= best_idx && best_idx < words_size@pre &&
      words_size == words_size@pre &&
      words == words@pre &&
      max == max &&
      cur == cur &&
      cmp == cmp &&
      i == words_size@pre &&
      j == j &&
      k == k &&
      len == len &&
      ch == ch &&
      0 <= maxu && maxu <= 128 &&
      0 <= unique && unique <= 128 &&
      rows_well_formed_158(rows, words_size@pre) &&
      problem_158_pre_z(rows) &&
      best_prefix_state_158(rows, words_size@pre, best_idx, maxu) &&
      problem_158_spec_z(rows, best_idx) &&
      Zlength(seen_l) == 128 &&
      CharPtrArray2::missing_i(words@pre, words_size@pre, best_idx, row_ptr, rows) *
      data_at(words@pre + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil)) *
      IntArray::full(seen, 128, seen_l)
    */
    max = words[best_idx];
    /*@ Assert
      exists row_ptr seen_l,
      0 <= best_idx && best_idx < words_size@pre &&
      words_size == words_size@pre &&
      words == words@pre &&
      max == row_ptr &&
      cur == cur &&
      cmp == cmp &&
      i == words_size@pre &&
      j == j &&
      k == k &&
      len == len &&
      ch == ch &&
      0 <= maxu && maxu <= 128 &&
      0 <= unique && unique <= 128 &&
      rows_well_formed_158(rows, words_size@pre) &&
      problem_158_pre_z(rows) &&
      best_prefix_state_158(rows, words_size@pre, best_idx, maxu) &&
      problem_158_spec_z(rows, best_idx) &&
      Zlength(seen_l) == 128 &&
      CharPtrArray2::missing_i(words@pre, words_size@pre, best_idx, row_ptr, rows) *
      data_at(words@pre + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil)) *
      IntArray::full(seen, 128, seen_l)
    */
    return max;
}
