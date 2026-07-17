/*
Write a function that accepts a vector of strings.  Return the word with the
maximum number of unique characters; break ties lexicographically.
*/

#include "ptr_array2_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq
      (problem_158_pre_z : list (list Z) -> Prop)
      (problem_158_spec_z : list (list Z) -> list Z -> Prop)
      (rows_well_formed_158 : list (list Z) -> Z -> Prop)
      (row_stores_158 : list Z -> list (list Z) -> Assertion)
      (row_stores_missing_i_158 : list Z -> list (list Z) -> Z -> Assertion)
      (row_stores_missing_two_158 : list Z -> list (list Z) -> Z -> Z -> Assertion)
      (seen_state_158 : list Z -> Z -> list Z -> Z -> Prop)
      (best_state_158 : list (list Z) -> Z -> Z -> Z -> Prop)
      (unique_count_z_158 : list Z -> Z)
      (Znth : {A} -> Z -> list A -> A -> A)
      (Zlength : {A} -> list A -> Z)
      (repeat_Z : {A} -> A -> Z -> list A)
 */
/*@ Import Coq Require Import coins_158 */

char *find_max(char **words, int words_size)
/*@ With ptrs rows
    Require
      0 < words_size && words_size < INT_MAX &&
      Zlength(ptrs) == words_size &&
      rows_well_formed_158(rows, words_size) &&
      problem_158_pre_z(rows) &&
      PtrArray::full(words, words_size, ptrs) *
      row_stores_158(ptrs, rows)
    Ensure exists best,
      0 <= best && best < words_size@pre &&
      __return == Znth(best, ptrs, 0) &&
      problem_158_spec_z(rows, Znth(best, rows, nil)) &&
      PtrArray::full(words@pre, words_size@pre, ptrs) *
      row_stores_158(ptrs, rows)
*/
{
    int best = 0;
    char *max = words[0];
    int maxu = 0;
    int i;

    /*@ Inv Assert
      0 <= i && i <= words_size@pre &&
      words == words@pre && words_size == words_size@pre &&
      0 < words_size@pre && words_size@pre < INT_MAX &&
      Zlength(ptrs) == words_size@pre &&
      rows_well_formed_158(rows, words_size@pre) &&
      problem_158_pre_z(rows) &&
      0 <= best && best < words_size@pre &&
      max == Znth(best, ptrs, 0) &&
      best_state_158(rows, i, best, maxu) &&
      PtrArray::full(words@pre, words_size@pre, ptrs) *
      row_stores_158(ptrs, rows)
    */
    for (i = 0; i < words_size; i++) {
        char *cur = words[i];
        int seen[256];
        int k;

        /*@ Inv Assert exists zeros,
          0 <= k && k <= 256 &&
          zeros == repeat_Z(0, k) &&
          0 <= i && i < words_size@pre &&
          words == words@pre && words_size == words_size@pre &&
          cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
          0 < words_size@pre && words_size@pre < INT_MAX &&
          0 <= best && best < words_size@pre &&
          Zlength(ptrs) == words_size@pre &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          best_state_158(rows, i, best, maxu) &&
          PtrArray::full(words@pre, words_size@pre, ptrs) *
          row_stores_158(ptrs, rows) *
          IntArray::seg(seen, 0, k, zeros) *
          IntArray::undef_seg(seen, k, 256)
        */
        for (k = 0; k < 256; k++) {
            seen[k] = 0;
        }

        /*@ Assert
          0 <= i && i < words_size@pre &&
          k == 256 && words == words@pre && words_size == words_size@pre &&
          cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
          0 < words_size@pre && words_size@pre < INT_MAX &&
          Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
          rows_well_formed_158(rows, words_size@pre) &&
          best_state_158(rows, i, best, maxu) &&
          PtrArray::full(words@pre, words_size@pre, ptrs) *
          row_stores_missing_i_158(ptrs, rows, i) *
          store_string(cur, Znth(i, rows, nil)) *
          IntArray::full(seen, 256, repeat_Z(0, 256))
        */
        int len = strlen(cur) /*@ where str = Znth(i, rows, nil) */;
        int unique = 0;
        int j;

        /*@ Inv Assert exists seen_l,
          0 <= j && j <= len &&
          len == string_length(Znth(i, rows, nil)) &&
          0 <= unique && unique <= j &&
          k == 256 && words == words@pre && words_size == words_size@pre &&
          0 <= i && i < words_size@pre &&
          cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
          0 <= best && best < words_size@pre &&
          0 < words_size@pre && words_size@pre < INT_MAX &&
          Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
          rows_well_formed_158(rows, words_size@pre) &&
          best_state_158(rows, i, best, maxu) &&
          seen_state_158(Znth(i, rows, nil), j, seen_l, unique) &&
          PtrArray::full(words@pre, words_size@pre, ptrs) *
          row_stores_missing_i_158(ptrs, rows, i) *
          store_string(cur, Znth(i, rows, nil)) *
          IntArray::full(seen, 256, seen_l)
        */
        for (j = 0; j < len; j++) {
            int ch = cur[j];
            /*@ Assert exists seen_l,
              0 <= j && j < len &&
              len == string_length(Znth(i, rows, nil)) &&
              0 <= unique && unique <= j &&
              0 <= ch && ch < 256 &&
              ch == Znth(j, Znth(i, rows, nil), 0) &&
              k == 256 && words == words@pre && words_size == words_size@pre &&
              0 <= i && i < words_size@pre &&
              cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
              0 <= best && best < words_size@pre &&
              0 < words_size@pre && words_size@pre < INT_MAX &&
              Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
              rows_well_formed_158(rows, words_size@pre) &&
              best_state_158(rows, i, best, maxu) &&
              seen_state_158(Znth(i, rows, nil), j, seen_l, unique) &&
              PtrArray::full(words@pre, words_size@pre, ptrs) *
              row_stores_missing_i_158(ptrs, rows, i) *
              store_string(cur, Znth(i, rows, nil)) *
              IntArray::full(seen, 256, seen_l)
            */
            if (seen[ch] == 0) {
                seen[ch] = 1;
                unique = unique + 1;
            }
        }

        /*@ Assert exists seen_l,
          0 <= i && i < words_size@pre &&
          j == len && k == 256 && len == len &&
          words == words@pre && words_size == words_size@pre &&
          cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
          unique == unique_count_z_158(Znth(i, rows, nil)) &&
          0 < words_size@pre && words_size@pre < INT_MAX &&
          Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
          rows_well_formed_158(rows, words_size@pre) &&
          best_state_158(rows, i, best, maxu) &&
          PtrArray::full(words@pre, words_size@pre, ptrs) *
          row_stores_158(ptrs, rows) *
          IntArray::full(seen, 256, seen_l)
        */

        int better = 0;
        int cmp = 0;
        if (unique > maxu) {
            better = 1;
        } else if (unique == maxu && i != best) {
            /*@ Assert exists seen_l,
              0 <= best && best < i && i < words_size@pre &&
              j == len && k == 256 && len == len &&
              words == words@pre && words_size == words_size@pre &&
              cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
              better == 0 && cmp == 0 &&
              unique == unique_count_z_158(Znth(i, rows, nil)) &&
              unique == maxu &&
              0 < words_size@pre && words_size@pre < INT_MAX &&
              Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
              rows_well_formed_158(rows, words_size@pre) &&
              best_state_158(rows, i, best, maxu) &&
              PtrArray::full(words@pre, words_size@pre, ptrs) *
              row_stores_missing_two_158(ptrs, rows, best, i) *
              store_string(max, Znth(best, rows, nil)) *
              store_string(cur, Znth(i, rows, nil)) *
              IntArray::full(seen, 256, seen_l)
            */
            cmp = strcmp(cur, max)
              /*@ where str1 = Znth(i, rows, nil),
                          str2 = Znth(best, rows, nil) */;
            /*@ Assert exists seen_l,
              0 <= best && best < i && i < words_size@pre &&
              j == len && k == 256 && len == len &&
              words == words@pre && words_size == words_size@pre &&
              cur == Znth(i, ptrs, 0) && max == Znth(best, ptrs, 0) &&
              better == 0 && cmp == cmp &&
              unique == unique_count_z_158(Znth(i, rows, nil)) &&
              unique == maxu &&
              strcmp_result(Znth(i, rows, nil), Znth(best, rows, nil), cmp) &&
              0 < words_size@pre && words_size@pre < INT_MAX &&
              Zlength(ptrs) == words_size@pre && problem_158_pre_z(rows) &&
              rows_well_formed_158(rows, words_size@pre) &&
              best_state_158(rows, i, best, maxu) &&
              PtrArray::full(words@pre, words_size@pre, ptrs) *
              row_stores_158(ptrs, rows) *
              IntArray::full(seen, 256, seen_l)
            */
            if (cmp < 0) {
                better = 1;
            }
        }

        if (better != 0) {
            max = cur;
            best = i;
            maxu = unique;
        }

        /*@ Assert exists seen_l,
          0 <= i && i < words_size@pre &&
          j == j && k == k && len == len && unique == unique &&
          better == better && cmp == cmp && cur == cur &&
          words == words@pre && words_size == words_size@pre &&
          0 < words_size@pre && words_size@pre < INT_MAX &&
          Zlength(ptrs) == words_size@pre &&
          rows_well_formed_158(rows, words_size@pre) &&
          problem_158_pre_z(rows) &&
          0 <= best && best < words_size@pre &&
          max == Znth(best, ptrs, 0) &&
          best_state_158(rows, i + 1, best, maxu) &&
          PtrArray::full(words@pre, words_size@pre, ptrs) *
          row_stores_158(ptrs, rows) *
          IntArray::full(seen, 256, seen_l)
        */
    }
    return max;
}
