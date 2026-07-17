/*
Task
We are given two strings s && c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a vector containing the result string && "True"/"False" for the check.
Example
For s = "abcde", c = "ae", the result should be ("bcd","False")
For s = "abcdef", c = "b"  the result should be ("acdef","False")
For s = "abcdedcba", c = "ab", the result should be ("cdedc","True")
*/

#include "verification_stdlib.h"
#include "ptr_array2_def.h"
#include "string.h"

/*@ Import Coq Require Import SimpleC.EE.coins_112 */

/*@ Extern Coq
      (problem_112_pre_z : list Z -> list Z -> Prop)
      (problem_112_spec_z : list Z -> list Z -> list Z -> Z -> Prop)
      (filter_not_in_z_112 : list Z -> list Z -> list Z)
      (filter_prefix_state_112 : list Z -> list Z -> Z -> list Z -> Prop)
      (palindrome_scan_state_112 : list Z -> Z -> Z -> Prop)
      (palindrome_result_112 : list Z -> Z -> Prop)
      (flag_payload_112 : Z -> list Z)
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

StrArray *reverse_delete(char *s, char *c)
/*@ With input removed s0 c0
    Require
      s == s0 && c == c0 &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      store_string(s, input) * store_string(c, removed)
    Ensure exists data filtered flag filtered_l pal,
      __return != 0 && data != 0 && filtered != 0 && flag != 0 &&
      (pal == 0 || pal == 1) &&
      problem_112_spec_z(input, removed, filtered_l, pal) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), 2) *
      PtrArray::full(data, 2, cons(filtered, cons(flag, nil))) *
      store_string(filtered, filtered_l) *
      CharArray::undef_seg(filtered, Zlength(filtered_l) + 1,
                           string_length(input) + 1) *
      store_string(flag, flag_payload_112(pal)) *
      store_string(s0, input) * store_string(c0, removed)
*/
{
    StrArray *out = malloc_str_array_struct();
    char **data = malloc_char_ptr_array(2);
    out->data = data;
    out->size = 2;

    int n = strlen(s) /*@ where str = input */;
    int k = 0;
    int i;
    char *filtered = malloc_char_array(n + 1);

    /*@ Inv Assert exists filtered_l,
      s == s0 && c == c0 &&
      n == string_length(input) &&
      k == Zlength(filtered_l) &&
      0 <= i && i <= n && 0 <= k && k <= i &&
      out != 0 && data != 0 && filtered != 0 &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      filter_prefix_state_112(input, removed, i, filtered_l) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 2) *
      PtrArray::undef_seg(data, 0, 2) *
      CharArray::full(filtered, k, filtered_l) *
      CharArray::undef_seg(filtered, k, n + 1) *
      store_string(s, input) * store_string(c, removed)
    */
    for (i = 0; i < n; i++) {
        int ch = s[i];
        /*@ Assert exists filtered_l,
          s == s0 && c == c0 &&
          n == string_length(input) &&
          k == Zlength(filtered_l) &&
          0 <= i && i < n && 0 <= k && k <= i &&
          ch == Znth(i, c_string(input), 0) &&
          0 <= ch && ch <= 127 &&
          out != 0 && data != 0 && filtered != 0 &&
          valid_string(input) && valid_string(removed) &&
          problem_112_pre_z(input, removed) &&
          string_length(input) + 2 < INT_MAX &&
          string_length(removed) < INT_MAX &&
          filter_prefix_state_112(input, removed, i, filtered_l) &&
          data_at(&(out -> data), data) *
          data_at(&(out -> size), 2) *
          PtrArray::undef_seg(data, 0, 2) *
          CharArray::full(filtered, k, filtered_l) *
          CharArray::undef_seg(filtered, k, n + 1) *
          store_string(s, input) * store_string(c, removed)
        */
        char *hit = strchr(c, ch) /*@ where str = removed */;
        if (hit == 0) {
            filtered[k] = ch;
            k = k + 1;
        }
    }
    filtered[k] = 0;
    int m = k;

    /*@ Assert
      s == s0 && c == c0 &&
      n == string_length(input) && i == n &&
      k == m && m == Zlength(filter_not_in_z_112(input, removed)) &&
      0 <= m && m <= n &&
      out != 0 && data != 0 && filtered != 0 &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 2) *
      PtrArray::undef_seg(data, 0, 2) *
      store_string(filtered, filter_not_in_z_112(input, removed)) *
      CharArray::undef_seg(filtered, m + 1, n + 1) *
      store_string(s, input) * store_string(c, removed)
    */

    int pal = 1;
    /*@ Assert
      s == s0 && c == c0 &&
      n == string_length(input) &&
      i == n &&
      k == m && m == Zlength(filter_not_in_z_112(input, removed)) &&
      0 <= m && m <= n && pal == 1 &&
      out != 0 && data != 0 && filtered != 0 &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 2) *
      PtrArray::undef_seg(data, 0, 2) *
      store_string(filtered, filter_not_in_z_112(input, removed)) *
      CharArray::undef_seg(filtered, m + 1, n + 1) *
      store_string(s, input) * store_string(c, removed)
    */
    /*@ Inv Assert
      s == s0 && c == c0 &&
      n == string_length(input) &&
      k == m && m == Zlength(filter_not_in_z_112(input, removed)) &&
      0 <= i && i <= m / 2 &&
      (pal == 0 || pal == 1) &&
      out != 0 && data != 0 && filtered != 0 &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      palindrome_scan_state_112(filter_not_in_z_112(input, removed), i, pal) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 2) *
      PtrArray::undef_seg(data, 0, 2) *
      store_string(filtered, filter_not_in_z_112(input, removed)) *
      CharArray::undef_seg(filtered, m + 1, n + 1) *
      store_string(s, input) * store_string(c, removed)
    */
    for (i = 0; i < m / 2; i++) {
        if (filtered[i] != filtered[m - 1 - i]) {
            pal = 0;
            /*@ Assert
              s == s0 && c == c0 &&
              n == string_length(input) &&
              k == m && m == Zlength(filter_not_in_z_112(input, removed)) &&
              0 <= i && i < m / 2 && pal == 0 &&
              out != 0 && data != 0 && filtered != 0 &&
              valid_string(input) && valid_string(removed) &&
              problem_112_pre_z(input, removed) &&
              string_length(input) + 2 < INT_MAX &&
              string_length(removed) < INT_MAX &&
              palindrome_scan_state_112(filter_not_in_z_112(input, removed), i + 1, pal) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), 2) *
              PtrArray::undef_seg(data, 0, 2) *
              store_string(filtered, filter_not_in_z_112(input, removed)) *
              CharArray::undef_seg(filtered, m + 1, n + 1) *
              store_string(s, input) * store_string(c, removed)
            */
            break;
        }
    }

    /*@ Assert
      s == s0 && c == c0 &&
      n == string_length(input) &&
      k == m && m == Zlength(filter_not_in_z_112(input, removed)) &&
      0 <= i && i <= m / 2 &&
      (pal == 0 || pal == 1) &&
      palindrome_result_112(filter_not_in_z_112(input, removed), pal) &&
      valid_string(input) && valid_string(removed) &&
      problem_112_pre_z(input, removed) &&
      string_length(input) + 2 < INT_MAX &&
      string_length(removed) < INT_MAX &&
      out != 0 && data != 0 && filtered != 0 &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 2) *
      PtrArray::undef_seg(data, 0, 2) *
      store_string(filtered, filter_not_in_z_112(input, removed)) *
      CharArray::undef_seg(filtered, m + 1, n + 1) *
      store_string(s, input) * store_string(c, removed)
    */

    char *flag;
    if (pal) {
        flag = malloc_char_array(5);
        flag[0] = 84;
        flag[1] = 114;
        flag[2] = 117;
        flag[3] = 101;
        flag[4] = 0;
    } else {
        flag = malloc_char_array(6);
        flag[0] = 70;
        flag[1] = 97;
        flag[2] = 108;
        flag[3] = 115;
        flag[4] = 101;
        flag[5] = 0;
    }

    data[0] = filtered;
    data[1] = flag;
    return out;
}
