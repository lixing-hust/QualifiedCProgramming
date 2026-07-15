/*
Write a function that takes a string && returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words && blank spaces in the sentence.

For example:
anti_shuffle("Hi") returns "Hi"
anti_shuffle("hello") returns "ehllo"
anti_shuffle("Hello World!!!") returns "Hello !!!Wdlor"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_86_pre_z: list Z -> Prop)
               (problem_86_spec_z: list Z -> list Z -> Prop)
               (anti_shuffle_safe_86: list Z -> Prop)
               (anti_shuffle_scan_state_86: list Z -> Z -> Z -> list Z -> list Z -> Prop)
               (anti_shuffle_nonspace_step_86: list Z -> Z -> Z -> list Z -> list Z -> Z -> Prop)
               (anti_shuffle_commit_step_86: list Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
               (anti_shuffle_commit_index_86: list Z -> Z -> Prop)
               (anti_shuffle_final_86: list Z -> list Z -> Prop)
               (sort_char_array_spec_86: list Z -> list Z -> Prop)
               (copy_prefix_86: list Z -> list Z -> Z -> list Z -> Prop)
               (out_sep_relation_86: Z -> list Z -> list Z -> Prop)
               (string_length: list Z -> Z)
               (Zlength: {A} -> list A -> Z) */
/*@ Import Coq Require Import coins_86 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

void free_char_array(char *array, int size)
/*@ Require
        array != 0 &&
        0 < size && size < INT_MAX &&
        CharArray::undef_full(array, size)
    Ensure emp
*/
;

void sort_char_array(char *array, int n)
/*@ With l
    Require
        array != 0 &&
        0 <= n && n < INT_MAX &&
        all_ascii(l) &&
        Zlength(l) == n &&
        CharArray::full(array, n, l)
    Ensure exists sorted_l,
        sort_char_array_spec_86(l, sorted_l) &&
        Zlength(sorted_l) == n &&
        all_ascii(sorted_l) &&
        CharArray::full(array, n, sorted_l)
*/
;

char* anti_shuffle(char *s)
/*@ With str_l
    Require
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_86_pre_z(str_l) &&
        anti_shuffle_safe_86(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        store_string(s, str_l)
    Ensure exists out_l,
        problem_86_spec_z(str_l, out_l) &&
        Zlength(out_l) == string_length(str_l) &&
        CharArray::full(__return, string_length(str_l) + 1, app(out_l, cons(0, nil))) *
        store_string(s, str_l)
*/
{
    int n = (int)strlen(s) /*@ where str = str_l */;
    char* out = malloc_char_array(n + 1);
    char* cur = malloc_char_array(n + 1);
    int out_len = 0;
    int cur_len = 0;
    int first = 1;
    int ch = 0;

    /*@ Inv Assert exists out_l cur_l,
        0 <= i && i <= n + 1 &&
        n == string_length(str_l) &&
        s == s@pre &&
        out != 0 &&
        cur != 0 &&
        0 <= out_len && out_len <= n &&
        0 <= cur_len && cur_len <= n &&
        Zlength(out_l) == out_len &&
        Zlength(cur_l) == cur_len &&
        (first == 0 || first == 1) &&
        0 <= ch && ch <= 127 &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_86_pre_z(str_l) &&
        anti_shuffle_safe_86(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
        store_string(s@pre, str_l) *
        CharArray::full(out, out_len, out_l) *
        CharArray::undef_seg(out, out_len, n + 1) *
        CharArray::full(cur, cur_len, cur_l) *
        CharArray::undef_seg(cur, cur_len, n + 1)
    */
    for (int i = 0; i <= n; i++)
    if (i < n && s[i] != 32)
    {
        ch = s[i];
        cur[cur_len] = ch;
        cur_len = cur_len + 1;
        /*@ Assert exists out_l cur_l,
            0 <= i && i < n &&
            n == string_length(str_l) &&
            s == s@pre &&
            out != 0 &&
            cur != 0 &&
            0 <= out_len && out_len <= n &&
            1 <= cur_len && cur_len <= n &&
            Zlength(out_l) == out_len &&
            Zlength(cur_l) == cur_len &&
            (first == 0 || first == 1) &&
            0 <= ch && ch <= 127 &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_86_pre_z(str_l) &&
            anti_shuffle_safe_86(str_l) &&
            string_length(str_l) + 1 < INT_MAX &&
            anti_shuffle_nonspace_step_86(str_l, i, first, out_l, cur_l, ch) &&
            anti_shuffle_scan_state_86(str_l, i + 1, first, out_l, cur_l) &&
            store_string(s@pre, str_l) *
            CharArray::full(out, out_len, out_l) *
            CharArray::undef_seg(out, out_len, n + 1) *
            CharArray::full(cur, cur_len, cur_l) *
            CharArray::undef_seg(cur, cur_len, n + 1)
        */
    }
    else
    {
        if (cur_len > 1) {
            sort_char_array(cur, cur_len);
            /*@ Assert exists out_l cur_l sorted_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                1 < cur_len && cur_len <= n &&
                Zlength(out_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                Zlength(sorted_l) == cur_len &&
                all_ascii(sorted_l) &&
                (first == 0 || first == 1) &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        } else {
            /*@ Assert exists out_l cur_l sorted_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                0 <= cur_len && cur_len <= 1 &&
                Zlength(out_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                sorted_l == cur_l &&
                Zlength(sorted_l) == cur_len &&
                all_ascii(sorted_l) &&
                (first == 0 || first == 1) &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        }
        if (first == 0) {
            out[out_len] = 32;
            out_len = out_len + 1;
            /*@ Assert exists out_l cur_l sorted_l out_sep_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                1 <= out_len && out_len <= n &&
                0 <= cur_len && cur_len <= n &&
                Zlength(out_l) == out_len - 1 &&
                out_sep_l == app(out_l, cons(32, nil)) &&
                Zlength(out_sep_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                Zlength(sorted_l) == cur_len &&
                all_ascii(sorted_l) &&
                first == 0 &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_sep_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        } else {
            /*@ Assert exists out_l cur_l sorted_l out_sep_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                0 <= cur_len && cur_len <= n &&
                Zlength(out_l) == out_len &&
                out_sep_l == out_l &&
                Zlength(out_sep_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                Zlength(sorted_l) == cur_len &&
                all_ascii(sorted_l) &&
                first == 1 &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_sep_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        }
        if (cur_len > 0) {
            int copy = 0;
            /*@ Inv Assert exists out_l cur_l sorted_l out_sep_l out_copy_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                0 < cur_len && cur_len <= n &&
                0 <= copy && copy <= cur_len &&
                out_len + cur_len <= n &&
                out_len + copy <= n &&
                Zlength(out_sep_l) == out_len &&
                Zlength(sorted_l) == cur_len &&
                Zlength(cur_l) == cur_len &&
                Zlength(out_copy_l) == out_len + copy &&
                copy_prefix_86(out_sep_l, sorted_l, copy, out_copy_l) &&
                out_sep_relation_86(first, out_l, out_sep_l) &&
                all_ascii(sorted_l) &&
                (first == 0 || first == 1) &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len + copy, out_copy_l) *
                CharArray::undef_seg(out, out_len + copy, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
            while (copy < cur_len) {
                ch = cur[copy];
                out[out_len + copy] = ch;
                copy = copy + 1;
                /*@ Assert exists out_l cur_l sorted_l out_sep_l out_copy_l,
                    0 <= i && i <= n &&
                    n == string_length(str_l) &&
                    s == s@pre &&
                    out != 0 &&
                    cur != 0 &&
                    0 <= out_len && out_len <= n &&
                    0 < cur_len && cur_len <= n &&
                    1 <= copy && copy <= cur_len &&
                    out_len + cur_len <= n &&
                    out_len + copy <= n &&
                    Zlength(out_sep_l) == out_len &&
                    Zlength(sorted_l) == cur_len &&
                    Zlength(cur_l) == cur_len &&
                    Zlength(out_copy_l) == out_len + copy &&
                    copy_prefix_86(out_sep_l, sorted_l, copy, out_copy_l) &&
                    out_sep_relation_86(first, out_l, out_sep_l) &&
                    all_ascii(sorted_l) &&
                    (first == 0 || first == 1) &&
                    0 <= ch && ch <= 127 &&
                    valid_string(str_l) &&
                    all_ascii(str_l) &&
                    problem_86_pre_z(str_l) &&
                    anti_shuffle_safe_86(str_l) &&
                    anti_shuffle_commit_index_86(str_l, i) &&
                    string_length(str_l) + 1 < INT_MAX &&
                    sort_char_array_spec_86(cur_l, sorted_l) &&
                    anti_shuffle_scan_state_86(str_l, i, first, out_l, cur_l) &&
                    store_string(s@pre, str_l) *
                    CharArray::full(out, out_len + copy, out_copy_l) *
                    CharArray::undef_seg(out, out_len + copy, n + 1) *
                    CharArray::full(cur, cur_len, sorted_l) *
                    CharArray::undef_seg(cur, cur_len, n + 1)
                */
            }
            out_len = out_len + cur_len;
            /*@ Assert exists out_l cur_l sorted_l out_sep_l out_next_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                0 < cur_len && cur_len <= n &&
                Zlength(out_sep_l) == out_len - cur_len &&
                Zlength(sorted_l) == cur_len &&
                out_next_l == app(out_sep_l, sorted_l) &&
                Zlength(out_next_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                copy == cur_len &&
                all_ascii(sorted_l) &&
                (first == 0 || first == 1) &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_commit_step_86(str_l, i, first, out_l, cur_l, out_next_l) &&
                anti_shuffle_scan_state_86(str_l, i + 1, 0, out_next_l, nil) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_next_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        } else {
            /*@ Assert exists out_l cur_l sorted_l out_sep_l out_next_l,
                0 <= i && i <= n &&
                n == string_length(str_l) &&
                s == s@pre &&
                out != 0 &&
                cur != 0 &&
                0 <= out_len && out_len <= n &&
                cur_len == 0 &&
                Zlength(out_sep_l) == out_len &&
                Zlength(sorted_l) == 0 &&
                out_next_l == out_sep_l &&
                Zlength(out_next_l) == out_len &&
                Zlength(cur_l) == cur_len &&
                all_ascii(sorted_l) &&
                (first == 0 || first == 1) &&
                0 <= ch && ch <= 127 &&
                valid_string(str_l) &&
                all_ascii(str_l) &&
                problem_86_pre_z(str_l) &&
                anti_shuffle_safe_86(str_l) &&
                anti_shuffle_commit_index_86(str_l, i) &&
                string_length(str_l) + 1 < INT_MAX &&
                sort_char_array_spec_86(cur_l, sorted_l) &&
                anti_shuffle_commit_step_86(str_l, i, first, out_l, cur_l, out_next_l) &&
                anti_shuffle_scan_state_86(str_l, i + 1, 0, out_next_l, nil) &&
                store_string(s@pre, str_l) *
                CharArray::full(out, out_len, out_next_l) *
                CharArray::undef_seg(out, out_len, n + 1) *
                CharArray::full(cur, cur_len, sorted_l) *
                CharArray::undef_seg(cur, cur_len, n + 1)
            */
        }
        cur_len = 0;
        first = 0;
        /*@ Assert exists out_next_l,
            0 <= i && i <= n &&
            n == string_length(str_l) &&
            s == s@pre &&
            out != 0 &&
            cur != 0 &&
            0 <= out_len && out_len <= n &&
            cur_len == 0 &&
            Zlength(out_next_l) == out_len &&
            first == 0 &&
            0 <= ch && ch <= 127 &&
            valid_string(str_l) &&
            all_ascii(str_l) &&
            problem_86_pre_z(str_l) &&
            anti_shuffle_safe_86(str_l) &&
            string_length(str_l) + 1 < INT_MAX &&
            anti_shuffle_scan_state_86(str_l, i + 1, first, out_next_l, nil) &&
            store_string(s@pre, str_l) *
            CharArray::full(out, out_len, out_next_l) *
            CharArray::undef_seg(out, out_len, n + 1) *
            CharArray::full(cur, cur_len, nil) *
            CharArray::undef_seg(cur, cur_len, n + 1)
        */
    }

    /*@ Assert exists out_l,
        n == string_length(str_l) &&
        s == s@pre &&
        out != 0 &&
        cur != 0 &&
        out_len == n &&
        cur_len == 0 &&
        first == 0 &&
        0 <= ch && ch <= 127 &&
        Zlength(out_l) == out_len &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_86_pre_z(str_l) &&
        anti_shuffle_safe_86(str_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        anti_shuffle_scan_state_86(str_l, n + 1, first, out_l, nil) &&
        anti_shuffle_final_86(str_l, out_l) &&
        problem_86_spec_z(str_l, out_l) &&
        store_string(s@pre, str_l) *
        CharArray::full(out, out_len, out_l) *
        CharArray::undef_seg(out, out_len, n + 1) *
        CharArray::full(cur, cur_len, nil) *
        CharArray::undef_seg(cur, cur_len, n + 1)
    */
    out[out_len] = 0;
    /*@ Assert exists out_l,
        n == string_length(str_l) &&
        s == s@pre &&
        out != 0 &&
        cur != 0 &&
        out_len == n &&
        cur_len == 0 &&
        first == 0 &&
        Zlength(out_l) == out_len &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_86_pre_z(str_l) &&
        problem_86_spec_z(str_l, out_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        data_at(&ch, ch) *
        store_string(s@pre, str_l) *
        CharArray::full(out, out_len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_full(cur, n + 1)
    */
    free_char_array(cur, n + 1);
    /*@ Assert exists out_l,
        n == string_length(str_l) &&
        s == s@pre &&
        out != 0 &&
        cur == cur &&
        out_len == n &&
        cur_len == 0 &&
        first == 0 &&
        Zlength(out_l) == out_len &&
        valid_string(str_l) &&
        all_ascii(str_l) &&
        problem_86_spec_z(str_l, out_l) &&
        string_length(str_l) + 1 < INT_MAX &&
        data_at(&ch, ch) *
        store_string(s@pre, str_l) *
        CharArray::full(out, out_len + 1, app(out_l, cons(0, nil)))
    */
    return out;
}
