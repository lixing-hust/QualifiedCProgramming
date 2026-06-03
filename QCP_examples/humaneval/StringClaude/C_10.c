/*
Find the shortest palindrome that begins with a supplied string.
Algorithm idea is simple:
- Find the longest postfix of supplied string that is a palindrome.
- Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
>>> make_palindrome("")
""
>>> make_palindrome("cat")
"catac"
>>> make_palindrome("cata")
"catac"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_10_pre_z: list Z -> Prop)
               (problem_10_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (pal_suffix_z: Z -> list Z -> Prop)
               (first_pal_suffix_z: Z -> list Z -> Prop)
               (make_pal_output_z: Z -> list Z -> list Z) */
/*@ Import Coq Require Import coins_10 */

int strlen(char *s)
/*@ With l len
    Require CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure __return == len &&
           CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
;

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int is_pal_suffix(char *s, int start, int n)
/*@ With l
    Require
        0 <= start && start <= n &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        ascii_range_z(l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
        ((__return == 1 && pal_suffix_z(start, l)) ||
         (__return == 0 && !(pal_suffix_z(start, l)))) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = start;
    int j = n - 1;

    if (start == n) {
        return 1;
    }

    /*@ Inv Assert
        s == s@pre &&
        start == start@pre &&
        n == n@pre &&
        0 <= start && start < n &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        ascii_range_z(l) &&
        start <= i && i <= n &&
        0 <= j && j < n &&
        i + j == n + start - 1 &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
        (forall (k: Z), (0 <= k && k < i - start) =>
            Znth(start + k, l, 0) == Znth(n - 1 - k, l, 0))
    */
    while (i < j) {
        if (s[i] != s[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}

char *make_palindrome(char *str)
/*@ With l len
    Require
        0 <= len && len < INT_MAX / 2 &&
        Zlength(l) == len &&
        problem_10_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
        problem_10_spec_z(l, out_l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil)))
*/
{
    int n = strlen(str) /*@ where l = l, len = len */;
    int best = n;
    int i;

    /*@ Inv Assert
        str == str@pre &&
        n == len &&
        0 <= n && n < INT_MAX / 2 &&
        Zlength(l) == n &&
        problem_10_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        0 <= best && best <= n &&
        ((best == n &&
          (forall (t: Z), (0 <= t && t < i) => !(pal_suffix_z(t, l)))) ||
         (best < n &&
          best < i &&
          pal_suffix_z(best, l) &&
          (forall (t: Z), (0 <= t && t < best) => !(pal_suffix_z(t, l))))) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (best == n) {
            int ok = is_pal_suffix(str, i, n) /*@ where l = l */;
            if (ok == 1) {
                best = i;
            }
        }
    }

    if (best == n) {
        best = 0;
    }

    int out_len = n + best;
    char *out = malloc_char_array(out_len + 1);

    /*@ Inv Assert
        exists out_l,
        str == str@pre &&
        n == len &&
        0 <= n && n < INT_MAX / 2 &&
        Zlength(l) == n &&
        problem_10_pre_z(l) &&
        ascii_range_z(l) &&
        first_pal_suffix_z(best, l) &&
        0 <= best && best <= n &&
        out_len == n + best &&
        out != 0 &&
        0 <= out_len && out_len < INT_MAX &&
        0 <= i && i <= n &&
        i <= out_len &&
        Zlength(out_l) == i &&
        (forall (p: Z), (0 <= p && p < i) =>
            Znth(p, out_l, 0) == Znth(p, l, 0)) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, i, out_l) *
        CharArray::undef_seg(out, i, out_len + 1)
    */
    for (i = 0; i < n; i++) {
        out[i] = str[i];
    }

    int k;
    /*@ Inv Assert
        exists out_l,
        str == str@pre &&
        n == len &&
        0 <= n && n < INT_MAX / 2 &&
        Zlength(l) == n &&
        problem_10_pre_z(l) &&
        ascii_range_z(l) &&
        first_pal_suffix_z(best, l) &&
        i == n &&
        0 <= best && best <= n &&
        out_len == n + best &&
        out != 0 &&
        0 <= out_len && out_len < INT_MAX &&
        0 <= k && k <= best &&
        n + k <= out_len &&
        Zlength(out_l) == n + k &&
        (forall (p: Z), (0 <= p && p < n) =>
            Znth(p, out_l, 0) == Znth(p, l, 0)) &&
        (forall (p: Z), (0 <= p && p < k) =>
            Znth(n + p, out_l, 0) == Znth(best - 1 - p, l, 0)) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, n + k, out_l) *
        CharArray::undef_seg(out, n + k, out_len + 1)
    */
    for (k = 0; k < best; k++) {
        out[n + k] = str[best - 1 - k];
    }

    out[out_len] = 0;
    /*@ Assert
        exists out_l,
        str == str@pre &&
        n == len &&
        0 <= n && n < INT_MAX / 2 &&
        Zlength(l) == n &&
        problem_10_pre_z(l) &&
        ascii_range_z(l) &&
        first_pal_suffix_z(best, l) &&
        0 <= best && best <= n &&
        i == n &&
        k == best &&
        out_l == make_pal_output_z(best, l) &&
        out != 0 &&
        0 <= out_len && out_len < INT_MAX &&
        out_len == Zlength(out_l) &&
        problem_10_spec_z(l, out_l) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, out_len + 1, app(out_l, cons(0, nil)))
    */
    return out;
}
