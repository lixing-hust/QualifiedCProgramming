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
#include "char_array_def.h"

/*@ Extern Coq (problem_86_pre_z: list Z -> Prop)
               (problem_86_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (sort_chars_z: list Z -> list Z)
               (anti_out_prefix_z: Z -> list Z -> list Z)
               (anti_cur_prefix_z: Z -> list Z -> list Z)
               (anti_shuffle_output_z: list Z -> list Z)
               (empty_z_list: list Z) */
/*@ Import Coq Require Import coins_86 */

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

void free_char_array(char *p, int init_size, int size)
/*@ With l
    Require
        p != 0 &&
        0 <= init_size && init_size <= size &&
        0 <= size &&
        Zlength(l) == init_size &&
        CharArray::full(p, init_size, l) *
        CharArray::undef_seg(p, init_size, size)
    Ensure emp
*/
;

void sort_char_array(char *p, int n)
/*@ With l
    Require
        0 <= n &&
        Zlength(l) == n &&
        CharArray::full(p, n, l)
    Ensure
        CharArray::full(p, n, sort_chars_z(l))
*/
;

void copy_char_array(char *dst, int off, char *src, int len, int cap)
/*@ With dst_l src_l
    Require
        0 <= off && 0 <= len &&
        off + len <= cap &&
        Zlength(dst_l) == off &&
        Zlength(src_l) == len &&
        CharArray::full(dst, off, dst_l) *
        CharArray::undef_seg(dst, off, cap) *
        CharArray::full(src, len, src_l)
    Ensure
        CharArray::full(dst, off + len, app(dst_l, src_l)) *
        CharArray::undef_seg(dst, off + len, cap) *
        CharArray::full(src, len, src_l)
*/
;

char* anti_shuffle(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_86_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
        problem_86_spec_z(l, out_l) &&
        CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil))) *
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s) /*@ where l = l, len = len */;
    int cap = n + 1;
    char *out = malloc_char_array(cap);
    char *cur = malloc_char_array(cap);
    int out_len = 0;
    int cur_len = 0;
    int i;

    /*@ Inv Assert
        s == s@pre &&
        n == len &&
        cap == n + 1 &&
        out != 0 &&
        cur != 0 &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_86_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        out_len == Zlength(anti_out_prefix_z(i, l)) &&
        cur_len == Zlength(anti_cur_prefix_z(i, l)) &&
        0 <= out_len && out_len <= n &&
        0 <= cur_len && cur_len <= n &&
        out_len + cur_len <= n &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, out_len, anti_out_prefix_z(i, l)) *
        CharArray::undef_seg(out, out_len, cap) *
        CharArray::full(cur, cur_len, anti_cur_prefix_z(i, l)) *
        CharArray::undef_seg(cur, cur_len, cap)
    */
    for (i = 0; i < n; i++) {
        if (s[i] != 32) {
            cur[cur_len] = s[i];
            cur_len = cur_len + 1;
        } else {
            sort_char_array(cur, cur_len) /*@ where l = anti_cur_prefix_z(i, l) */;
            copy_char_array(out, out_len, cur, cur_len, cap)
                /*@ where dst_l = anti_out_prefix_z(i, l),
                          src_l = sort_chars_z(anti_cur_prefix_z(i, l)) */;
            out_len = out_len + cur_len;
            cur_len = 0;
            out[out_len] = 32;
            out_len = out_len + 1;
        }
    }

    sort_char_array(cur, cur_len) /*@ where l = anti_cur_prefix_z(n, l) */;
    copy_char_array(out, out_len, cur, cur_len, cap)
        /*@ where dst_l = anti_out_prefix_z(n, l),
                  src_l = sort_chars_z(anti_cur_prefix_z(n, l)) */;
    out_len = out_len + cur_len;
    free_char_array(cur, cur_len, cap)
        /*@ where l = sort_chars_z(anti_cur_prefix_z(n, l)) */;
    cur_len = 0;

    out[out_len] = 0;
    /*@ Assert
        s == s@pre &&
        n == len &&
        cap == n + 1 &&
        out != 0 &&
        cur != 0 &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_86_pre_z(l) &&
        ascii_range_z(l) &&
        i == n &&
        out_len == Zlength(anti_shuffle_output_z(l)) &&
        cur_len == 0 &&
        problem_86_spec_z(l, anti_shuffle_output_z(l)) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, out_len + 1, app(anti_shuffle_output_z(l), cons(0, nil))) *
        CharArray::undef_seg(out, out_len + 1, cap)
    */
    return out;
}
