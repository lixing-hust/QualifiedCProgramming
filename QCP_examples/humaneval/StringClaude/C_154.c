/*
You are given 2 words. You need to return true if the second word or any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => false
cycpattern_check("hello","ell") => true
cycpattern_check("whassup","psus") => false
cycpattern_check("abab","baa") => true
cycpattern_check("efef","eeff") => false
cycpattern_check("himenss","simen") => true

*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_154_pre_z: list Z -> list Z -> Prop)
               (problem_154_spec_z: list Z -> list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (rot_index_z: Z -> Z -> Z -> Z)
               (rotation_match_progress_z: Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
               (rotation_match_at_z: Z -> Z -> list Z -> list Z -> Prop)
               (rotation_shift_search_z: Z -> Z -> Z -> list Z -> list Z -> Prop)
               (rotation_shift_has_match_z: Z -> list Z -> list Z -> Prop)
               (rotation_any_search_z: Z -> Z -> list Z -> list Z -> Prop)
               (rotation_any_match_z: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_154 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int rotation_match_at(char *a, char *b, int pos, int shift, int n, int m)
/*@ With a_l b_l
    Require
        0 <= n && n < INT_MAX &&
        0 < m && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        0 <= pos && pos + m <= n &&
        0 <= shift && shift < m &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        ((__return == 1 && rotation_match_at_z(pos, shift, a_l, b_l)) ||
         (__return == 0 && !(rotation_match_at_z(pos, shift, a_l, b_l)))) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int ok = 1;
    int j;

    /*@ Inv Assert
        a == a@pre &&
        b == b@pre &&
        pos == pos@pre &&
        shift == shift@pre &&
        n == n@pre &&
        m == m@pre &&
        0 <= n && n < INT_MAX &&
        0 < m && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        0 <= pos && pos + m <= n &&
        0 <= shift && shift < m &&
        0 <= j && j <= m &&
        (ok == 0 || ok == 1) &&
        rotation_match_progress_z(pos, shift, j, ok, a_l, b_l) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    */
    for (j = 0; j < m; j++) {
        int idx = shift + j;
        if (idx >= m) {
            idx = idx - m;
        }
        /*@ Assert
            a == a@pre &&
            b == b@pre &&
            pos == pos@pre &&
            shift == shift@pre &&
            n == n@pre &&
            m == m@pre &&
            0 <= n && n < INT_MAX &&
            0 < m && m < INT_MAX / 2 &&
            Zlength(a_l) == n &&
            Zlength(b_l) == m &&
            ascii_range_z(a_l) &&
            ascii_range_z(b_l) &&
            0 <= pos && pos + m <= n &&
            0 <= shift && shift < m &&
            0 <= j && j < m &&
            0 <= idx && idx < m &&
            idx == rot_index_z(shift, j, m) &&
            (ok == 0 || ok == 1) &&
            rotation_match_progress_z(pos, shift, j, ok, a_l, b_l) &&
            CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
            CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
        */
        if (a[pos + j] != b[idx]) {
            ok = 0;
        }
    }
    return ok;
}

int rotation_occurs_at_shift(char *a, char *b, int shift, int n, int m)
/*@ With a_l b_l
    Require
        0 <= n && n < INT_MAX &&
        0 < m && m <= n && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        0 <= shift && shift < m &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        ((__return == 1 && rotation_shift_has_match_z(shift, a_l, b_l)) ||
         (__return == 0 && !(rotation_shift_has_match_z(shift, a_l, b_l)))) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int found = 0;
    int pos;

    /*@ Inv Assert
        a == a@pre &&
        b == b@pre &&
        shift == shift@pre &&
        n == n@pre &&
        m == m@pre &&
        0 <= n && n < INT_MAX &&
        0 < m && m <= n && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        0 <= shift && shift < m &&
        0 <= pos && pos <= n - m + 1 &&
        (found == 0 || found == 1) &&
        rotation_shift_search_z(shift, pos, found, a_l, b_l) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    */
    for (pos = 0; pos <= n - m; pos++) {
        int ok = rotation_match_at(a, b, pos, shift, n, m) /*@ where a_l = a_l, b_l = b_l */;
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}

int cycpattern_check(char *a, char *b)
/*@ With a_l n b_l m
    Require
        0 <= n && n < INT_MAX &&
        0 <= m && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        problem_154_pre_z(a_l, b_l) &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        problem_154_spec_z(a_l, b_l, __return) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int n0 = strlen(a) /*@ where l = a_l, n = n */;
    int m0 = strlen(b) /*@ where l = b_l, n = m */;

    if (m0 == 0) {
        return 1;
    }
    if (m0 > n0) {
        return 0;
    }

    int found = 0;
    int shift;

    /*@ Inv Assert
        a == a@pre &&
        b == b@pre &&
        n0 == n &&
        m0 == m &&
        0 <= n && n < INT_MAX &&
        0 < m && m <= n && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        problem_154_pre_z(a_l, b_l) &&
        ascii_range_z(a_l) &&
        ascii_range_z(b_l) &&
        0 <= shift && shift <= m &&
        (found == 0 || found == 1) &&
        rotation_any_search_z(shift, found, a_l, b_l) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    */
    for (shift = 0; shift < m0; shift++) {
        int ok = rotation_occurs_at_shift(a, b, shift, n0, m0) /*@ where a_l = a_l, b_l = b_l */;
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}
