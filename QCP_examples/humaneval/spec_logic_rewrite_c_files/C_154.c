#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "../../stdlib/string.h"

/*@ Extern Coq
      (problem_154_pre_z : list Z -> list Z -> Prop)
      (problem_154_spec_z : list Z -> list Z -> Z -> Prop)
      (rotate_at_154 : list Z -> Z -> list Z)
      (rotation_prefix_154 : list Z -> Z -> Z -> list Z -> Prop)
      (rotation_scan_state_154 : list Z -> list Z -> Z -> Prop)
      (rotation_success_154 : list Z -> list Z -> Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import coins_154 */

char *malloc_char_array(int n)
/*@ Require 0 <= n && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

void free_char_array(char *p, int n)
/*@ Require p != 0 && 0 <= n && n < INT_MAX &&
            CharArray::undef_full(p, n)
    Ensure emp
*/
;

int cycpattern_check(char *a, char *b)
/*@ With a_l b_l (a0: Z) (b0: Z)
    Require
      a == a0 && b == b0 &&
      problem_154_pre_z(a_l, b_l) &&
      valid_string(a_l) && valid_string(b_l) &&
      string_length(a_l) < INT_MAX &&
      string_length(b_l) + 1 < INT_MAX &&
      store_string(a0, a_l) * store_string(b0, b_l)
    Ensure
      (__return == 0 || __return == 1) &&
      problem_154_spec_z(a_l, b_l, __return) &&
      store_string(a0, a_l) * store_string(b0, b_l)
*/
{
    int n = strlen(b) /*@ where str = b_l */;
    char *rotate = malloc_char_array(n + 1);
    if (rotate == 0) return 0;

    int i = 0;
    /*@ Inv Assert
          0 <= i && i <= n &&
          rotate != 0 &&
          n + 1 < INT_MAX &&
          a == a0 && b == b0 &&
          valid_string(a_l) && valid_string(b_l) &&
          string_length(a_l) < INT_MAX &&
          n == string_length(b_l) &&
          rotation_scan_state_154(a_l, b_l, i) &&
          store_string(a, a_l) *
          store_string(b, b_l) *
          CharArray::undef_full(rotate, n + 1)
    */
    while (i < n)
    {
        {
            int j = 0;
            /*@ Inv Assert
              exists rotate_l,
              0 <= j && j <= n &&
              0 < n && 0 <= i && i < n &&
              rotate != 0 &&
              n + 1 < INT_MAX &&
              a == a0 && b == b0 &&
              valid_string(a_l) && valid_string(b_l) &&
              string_length(a_l) < INT_MAX &&
              n == string_length(b_l) &&
              rotation_scan_state_154(a_l, b_l, i) &&
              rotation_prefix_154(b_l, i, j, rotate_l) &&
              store_string(a, a_l) *
              store_string(b, b_l) *
              CharArray::full(rotate, j, rotate_l) *
              CharArray::undef_seg(rotate, j, n + 1)
            */
            while (j < n)
            {
                {
                int idx;
                if (j >= n - i) {
                    idx = j - (n - i);
                } else {
                    idx = i + j;
                }
                /*@ Assert
                      idx == (i + j) % n &&
                      0 <= idx && idx < n &&
                      exists rotate_l,
                      0 <= j && j < n &&
                      0 < n && 0 <= i && i < n &&
                      rotate != 0 &&
                      n + 1 < INT_MAX &&
                      a == a0 && b == b0 &&
                      valid_string(a_l) && valid_string(b_l) &&
                      string_length(a_l) < INT_MAX &&
                      n == string_length(b_l) &&
                      rotation_scan_state_154(a_l, b_l, i) &&
                      rotation_prefix_154(b_l, i, j, rotate_l) &&
                      store_string(a, a_l) *
                      store_string(b, b_l) *
                      CharArray::full(rotate, j, rotate_l) *
                      CharArray::undef_seg(rotate, j, n + 1)
                */
                int ch = b[idx];
                /*@ Assert
                      ch == Znth(idx, b_l, 0) &&
                      idx == (i + j) % n &&
                      0 <= ch && ch <= 127 &&
                      0 <= idx && idx < n &&
                      exists rotate_l,
                      0 <= j && j < n &&
                      0 < n && 0 <= i && i < n &&
                      rotate != 0 &&
                      n + 1 < INT_MAX &&
                      a == a0 && b == b0 &&
                      valid_string(a_l) && valid_string(b_l) &&
                      string_length(a_l) < INT_MAX &&
                      n == string_length(b_l) &&
                      rotation_scan_state_154(a_l, b_l, i) &&
                      rotation_prefix_154(b_l, i, j, rotate_l) &&
                      store_string(a, a_l) *
                      store_string(b, b_l) *
                      CharArray::full(rotate, j, rotate_l) *
                      CharArray::undef_seg(rotate, j, n + 1)
                */
                rotate[j] = ch;
                }
                j++;
            }
        }

        rotate[n] = 0;
        /*@ Assert
              rotate != 0 &&
              n + 1 < INT_MAX &&
              a == a0 && b == b0 &&
              valid_string(a_l) && valid_string(b_l) &&
              string_length(a_l) < INT_MAX &&
              n == string_length(b_l) &&
              rotation_scan_state_154(a_l, b_l, i) &&
              rotation_prefix_154(b_l, i, n, rotate_at_154(b_l, i)) &&
              valid_string(rotate_at_154(b_l, i)) &&
              store_string(a, a_l) *
              store_string(b, b_l) *
              store_string(rotate, rotate_at_154(b_l, i))
        */

        char *hit = strstr(a, rotate)
                    /*@ where str1 = a_l, str2 = rotate_at_154(b_l, i) */;
        if (hit != 0) {
            /*@ Assert
                  hit != 0 &&
                  rotate != 0 &&
                  n + 1 < INT_MAX &&
                  a == a0 && b == b0 &&
                  valid_string(a_l) && valid_string(b_l) &&
                  string_length(a_l) < INT_MAX &&
                  n == string_length(b_l) &&
                  rotation_success_154(a_l, b_l, i, rotate_at_154(b_l, i)) &&
                  store_string(a, a_l) *
                  store_string(b, b_l) *
                  CharArray::undef_full(rotate, n + 1)
            */
            free_char_array(rotate, n + 1);
            return 1;
        }

        /*@ Assert
              hit == 0 &&
              rotate != 0 &&
              n + 1 < INT_MAX &&
              a == a0 && b == b0 &&
              valid_string(a_l) && valid_string(b_l) &&
              string_length(a_l) < INT_MAX &&
              n == string_length(b_l) &&
              rotation_scan_state_154(a_l, b_l, i + 1) &&
              store_string(a, a_l) *
              store_string(b, b_l) *
              CharArray::undef_full(rotate, n + 1)
        */
        i++;
    }

    free_char_array(rotate, n + 1);
    return 0;
}
