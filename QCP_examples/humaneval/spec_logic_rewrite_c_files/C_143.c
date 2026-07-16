/*
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original
sentence whose lengths are prime numbers, preserving their order.
*/

#include "verification_list.h"
#include "char_array_def.h"
#include "string.h"

/*@ Import Coq Require Import SimpleC.EE.coins_143 */

/*@ Extern Coq
      (problem_143_pre_z : list Z -> Prop)
      (problem_143_spec_z : list Z -> list Z -> Prop)
      (ascii_range_z_143 : list Z -> Prop)
      (SpaceFreeZ143 : list Z -> Prop)
      (SentencePrefix143 : list Z -> Z -> list Z -> list (list Z) -> Prop)
      (PrimeLengthWordsZ143 : list (list Z) -> list (list Z) -> Prop)
      (join_words_z_143 : list (list Z) -> list Z)
      (copy_prefix_143 : list Z -> list Z -> Prop)
      (min_z_143 : Z -> Z -> Z)
      (current_word_143 : list Z -> Z -> Z -> list Z -> Prop)
      (prime_scan_state_143 : Z -> Z -> Z -> Prop)
      (output_gap_outer_143 : Z -> Z -> Z -> Prop)
      (output_gap_inner_143 : Z -> Z -> Prop)
      (output_gap_copy_143 : Z -> Z -> Prop)
      (word_boundary_143 : list Z -> Z -> Z -> Prop)
      (outer_done_143 : Z -> Z -> Z -> Prop)
 */

char *malloc_char_array(int n)
/*@ Require 0 < n && n <= INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char *words_in_sentence(char *sentence)
/*@ With input sentence_addr
    Require sentence == sentence_addr &&
            problem_143_pre_z(input) &&
            ascii_range_z_143(input) &&
            valid_string(input) &&
            store_string(sentence, input)
    Ensure exists output,
             __return != 0 &&
             problem_143_spec_z(input, output) &&
             store_string(sentence_addr, input) *
             store_string(__return, output) *
             CharArray::undef_seg(__return,
                                  string_length(output) + 1,
                                  string_length(input) + 1)
*/
{
    int n = strlen(sentence) /*@ where str = input */;
    char *out = malloc_char_array(n + 1);
    int out_len = 0;
    int start = -1;
    int i = 0;
    int isp = 0;
    int l = 0;
    int j = 0;

    /*@ Inv Assert
        exists cur words selected output_l,
          0 <= i && i <= n + 1 &&
          0 <= out_len && out_len <= i && out_len <= n &&
          output_gap_outer_143(out_len, start, i) &&
          outer_done_143(i, n, start) &&
          sentence == sentence_addr &&
          out != 0 &&
          INT_MIN <= isp && isp <= INT_MAX &&
          INT_MIN <= l && l <= INT_MAX &&
          INT_MIN <= j && j <= INT_MAX &&
          Zlength(output_l) == out_len &&
          SentencePrefix143(input, min_z_143(i, n), cur, words) &&
          PrimeLengthWordsZ143(words, selected) &&
          output_l == join_words_z_143(selected) &&
          current_word_143(input, min_z_143(i, n), start, cur) &&
          n == string_length(input) &&
          problem_143_pre_z(input) &&
          ascii_range_z_143(input) &&
          valid_string(input) &&
          store_string(sentence, input) *
          CharArray::full(out, out_len, output_l) *
          CharArray::undef_seg(out, out_len, n + 1)
    */
    while (i <= n)
    {
        if (i < n && sentence[i] != ' ') {
            if (start < 0) {
                start = i;
            }
        } else {
            if (start >= 0) {
                isp = 1;
                l = i - start;
                if (l < 2) {
                    isp = 0;
                }
                j = 2;
                /*@ Inv Assert
                    exists cur words selected output_l,
                      0 <= i && i <= n &&
                      0 <= start && start < i &&
                      l == i - start && 0 < l && l <= 100 &&
                      2 <= j && j <= 12 &&
                      INT_MIN <= isp && isp <= INT_MAX &&
                      0 <= out_len && out_len <= i &&
                      output_gap_inner_143(out_len, start) &&
                      word_boundary_143(input, i, n) &&
                      sentence == sentence_addr &&
                      out != 0 &&
                      Zlength(output_l) == out_len &&
                      SentencePrefix143(input, i, cur, words) &&
                      PrimeLengthWordsZ143(words, selected) &&
                      output_l == join_words_z_143(selected) &&
                      current_word_143(input, i, start, cur) &&
                      prime_scan_state_143(l, j, isp) &&
                      n == string_length(input) &&
                      problem_143_pre_z(input) &&
                      ascii_range_z_143(input) &&
                      valid_string(input) &&
                      store_string(sentence, input) *
                      CharArray::full(out, out_len, output_l) *
                      CharArray::undef_seg(out, out_len, n + 1)
                */
                while (j * j <= l)
                {
                    if (l % j == 0) {
                        isp = 0;
                    }
                    j++;
                }

                if (isp) {
                    if (out_len > 0) {
                        out[out_len] = ' ';
                        out_len++;
                    }
                    /*@ Assert
                        exists cur words selected old_output
                               input_pre input_post output_pre,
                          Zlength(sublist(start, i, input)) == l &&
                          all_ascii(sublist(start, i, input)) &&
                          0 <= l && l < INT_MAX &&
                          0 <= start && start < i && i <= n &&
                          0 <= out_len && out_len + l <= n &&
                          output_gap_copy_143(out_len, start) &&
                          word_boundary_143(input, i, n) &&
                          isp != 0 &&
                          j * j > l &&
                          INT_MIN <= isp && isp <= INT_MAX &&
                          INT_MIN <= j && j <= INT_MAX &&
                          sentence == sentence_addr &&
                          out != 0 &&
                          n == string_length(input) &&
                          problem_143_pre_z(input) &&
                          ascii_range_z_143(input) &&
                          valid_string(input) &&
                          SentencePrefix143(input, i, cur, words) &&
                          PrimeLengthWordsZ143(words, selected) &&
                          old_output == join_words_z_143(selected) &&
                          current_word_143(input, i, start, cur) &&
                          prime_scan_state_143(l, j, isp) &&
                          copy_prefix_143(old_output, output_pre) &&
                          Zlength(output_pre) == out_len &&
                          input_pre == sublist(0, start, c_string(input)) &&
                          input_post == sublist(i, n + 1, c_string(input)) &&
                          CharArray::full(out, out_len, output_pre) *
                          CharArray::undef_full(out + out_len * sizeof(char), l) *
                          CharArray::undef_seg(out, out_len + l, n + 1) *
                          CharArray::seg(sentence, 0, start, input_pre) *
                          CharArray::full(sentence + start * sizeof(char), l,
                                          sublist(start, i, input)) *
                          CharArray::seg(sentence, i, n + 1, input_post)
                    */
                    memcpy(out + out_len, sentence + start, l)
                        /*@ where bytes = sublist(start, i, input) */;
                    out_len += l;
                }
                start = -1;
            }
        }
        i++;
    }

    out[out_len] = '\0';
    return out;
}
