/*
You will be given a string of words separated by commas or spaces. Your task is
to split the string into words and return an array of the words.

For example:
words_string("Hi, my name is John") == {"Hi", "my", "name", "is", "John"}
words_string("One, two, three, four, five, six") ==
    {"One", "two", "three", "four", "five", "six"}
*/

#include "ptr_array2_def.h"
#include "char_array_def.h"
#include "string.h"

/*@ Import Coq Require Import SimpleC.EE.coins_101 */

/*@ Extern Coq
      (problem_101_pre_z : list Z -> Prop)
      (problem_101_spec_z : list Z -> list (list Z) -> Prop)
      (split_prefix_state_101 :
         list Z -> Z -> Z -> list (list Z) -> Prop)
      (closing_delimiter_101 : list Z -> Z -> Z -> Prop)
      (words_rows_heap_101 : list Z -> list (list Z) -> Assertion)
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

char *malloc_char_array(int size)
/*@ Require 0 < size && size < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/
;

StrArray *words_string(char *s)
/*@ With input input_ptr
    Require s == input_ptr &&
            problem_101_pre_z(input) &&
            valid_string(input) &&
            2 * (string_length(input) + 1) < INT_MAX &&
            store_string(s, input)
    Ensure exists data output_words output_ptrs output_size cap,
      __return != 0 && data != 0 &&
      0 <= output_size && output_size <= string_length(input) + 1 &&
      output_size == Zlength(output_words) &&
      output_size == Zlength(output_ptrs) &&
      output_size <= cap && cap < INT_MAX &&
      problem_101_spec_z(input, output_words) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      store_string(input_ptr, input) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, cap) *
      words_rows_heap_101(output_ptrs, output_words)
*/
{
    StrArray *out = malloc_str_array_struct();
    int output_size = 0;
    int start = -1;
    int n = strlen(s) /*@ where str = input */;
    int cap = n + 1;
    char **data = malloc_char_ptr_array(cap);
    out->data = data;
    out->size = 0;

    /*@ Inv Assert exists output_words output_ptrs,
      0 <= i && i <= n + 1 &&
      n == string_length(input) &&
      0 <= output_size && output_size <= i &&
      output_size == Zlength(output_words) &&
      output_size == Zlength(output_ptrs) &&
      cap == n + 1 && 0 <= cap && cap < INT_MAX &&
      output_size <= cap &&
      out != 0 && data != 0 &&
      s == input_ptr &&
      split_prefix_state_101(input, i, start, output_words) &&
      problem_101_pre_z(input) &&
      valid_string(input) &&
      2 * (string_length(input) + 1) < INT_MAX &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), output_size) *
      store_string(s, input) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, cap) *
      words_rows_heap_101(output_ptrs, output_words)
    */
    for (int i = 0; i <= n; i++) {
        char ch;
        if (i < n) {
            ch = s[i];
        } else {
            ch = ' ';
        }

        if (ch == ' ' || ch == ',') {
            if (start >= 0) {
                int len = i - start;
                char *w = malloc_char_array(len + 1);

                /*@ Assert exists input_pre input_post output_words output_ptrs,
                  0 <= start && start < i && i <= n &&
                  len == i - start &&
                  Zlength(sublist(start, i, input)) == len &&
                  all_ascii(sublist(start, i, input)) &&
                  input_pre == sublist(0, start, c_string(input)) &&
                  input_post == sublist(i, n + 1, c_string(input)) &&
                  n == string_length(input) &&
                  0 <= output_size && output_size <= i &&
                  output_size == Zlength(output_words) &&
                  output_size == Zlength(output_ptrs) &&
                  output_size <= cap &&
                  cap == n + 1 && 0 <= cap && cap < INT_MAX &&
                  out != 0 && data != 0 && w != 0 && ch == ch &&
                  s == input_ptr &&
                  closing_delimiter_101(input, i, n) &&
                  split_prefix_state_101(input, i, start, output_words) &&
                  problem_101_pre_z(input) && valid_string(input) &&
                  2 * (string_length(input) + 1) < INT_MAX &&
                  data_at(&(out -> data), data) *
                  data_at(&(out -> size), output_size) *
                  CharArray::seg(s, 0, start, input_pre) *
                  CharArray::full(s + start * sizeof(char), len,
                                  sublist(start, i, input)) *
                  CharArray::seg(s, i, n + 1, input_post) *
                  CharArray::undef_full(w, len) *
                  CharArray::undef_seg(w, len, len + 1) *
                  PtrArray::seg(data, 0, output_size, output_ptrs) *
                  PtrArray::undef_seg(data, output_size, cap) *
                  words_rows_heap_101(output_ptrs, output_words)
                */
                memcpy(w, s + start, len)
                    /*@ where bytes = sublist(start, i, input) */;
                w[len] = '\0';

                /*@ Assert exists output_words output_ptrs,
                  0 <= start && start < i && i <= n &&
                  len == i - start &&
                  n == string_length(input) &&
                  0 <= output_size && output_size <= i &&
                  output_size == Zlength(output_words) &&
                  output_size == Zlength(output_ptrs) &&
                  output_size < cap &&
                  cap == n + 1 && 0 <= cap && cap < INT_MAX &&
                  out != 0 && data != 0 && w != 0 && ch == ch &&
                  s == input_ptr &&
                  closing_delimiter_101(input, i, n) &&
                  split_prefix_state_101(input, i, start, output_words) &&
                  problem_101_pre_z(input) && valid_string(input) &&
                  2 * (string_length(input) + 1) < INT_MAX &&
                  data_at(&(out -> data), data) *
                  data_at(&(out -> size), output_size) *
                  store_string(s, input) *
                  CharArray::full(w,
                    Zlength(c_string(sublist(start, i, input))),
                    c_string(sublist(start, i, input))) *
                  PtrArray::seg(data, 0, output_size, output_ptrs) *
                  PtrArray::undef_seg(data, output_size, cap) *
                  words_rows_heap_101(output_ptrs, output_words)
                */
                data[output_size] = w;
                output_size++;
                out->size = output_size;
                start = -1;
            }
        } else if (start < 0) {
            start = i;
        }
    }
    return out;
}
