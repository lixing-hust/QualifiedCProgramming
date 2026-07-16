/*
You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "string.h"

/*@ Extern Coq (problem_161_pre_z: list Z -> Prop)
               (problem_161_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (lower_z_161: Z -> Prop)
               (upper_z_161: Z -> Prop)
               (flip_char_z_161: Z -> Z)
               (flip_scan_state_z_161: list Z -> list Z -> Z -> Z -> Prop)
               (reverse_scan_state_z_161: list Z -> list Z -> Z -> Prop)
               (has_letter_z_161: list Z -> Prop)
               (no_letter_z_161: list Z -> Prop)
               (flip_output_z_161: list Z -> list Z -> Prop)
               (reverse_output_z_161: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_161 */

char *malloc_char_array(int n)
/*@ Require n > 0 && n <= INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

void free_char_array(char *array, int size)
/*@ Require array != 0 && 0 < size && size <= INT_MAX &&
            exists bytes,
              Zlength(bytes) == size && CharArray::full(array, size, bytes)
    Ensure emp
*/
;

char *solve(char *s)
/*@ With input
    Require
        valid_string(input) &&
        problem_161_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(s, input)
    Ensure exists output,
        problem_161_spec_z(input, output) &&
        valid_string(output) &&
        store_string(s, input) *
        store_string(__return, output)
*/
{
    int n = strlen(s) /*@ where str = input */;
    int nletter = 0;
    char *out = malloc_char_array(n + 1);
    if (out == 0) return 0;

    int i;
    int w = 0;
    /*@ Inv Assert exists output,
        s == s@pre &&
        n == string_length(input) &&
        out != 0 &&
        0 <= i && i <= n &&
        0 <= nletter && nletter <= i &&
        0 <= w && w <= 127 &&
        flip_scan_state_z_161(input, output, i, nletter) &&
        valid_string(input) &&
        problem_161_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(s@pre, input) *
        CharArray::full(out, i, output) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        w = s[i];
        if (w >= 65 && w <= 90) {
            w = w + 32;
        } else if (w >= 97 && w <= 122) {
            w = w - 32;
        } else {
            nletter = nletter + 1;
        }
        out[i] = w;
        /*@ Assert exists output,
            s == s@pre &&
            n == string_length(input) &&
            out != 0 &&
            0 <= i && i < n &&
            0 <= nletter && nletter <= i + 1 &&
            0 <= w && w <= 127 &&
            flip_scan_state_z_161(input, output, i + 1, nletter) &&
            valid_string(input) &&
            problem_161_pre_z(input) &&
            ascii_range_z(input) &&
            string_length(input) < INT_MAX &&
            store_string(s@pre, input) *
            CharArray::full(out, i + 1, output) *
            CharArray::undef_seg(out, i + 1, n + 1)
        */
    }

    /*@ Assert exists output,
        s == s@pre &&
        n == string_length(input) &&
        i == n &&
        out != 0 &&
        0 <= nletter && nletter <= n &&
        w == w &&
        flip_scan_state_z_161(input, output, n, nletter) &&
        valid_string(input) &&
        problem_161_pre_z(input) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(s@pre, input) *
        CharArray::full(out, n, output) *
        CharArray::undef_seg(out, n, n + 1)
    */
    out[n] = 0;

    if (nletter == n) {
        /*@ Assert exists output,
            s == s@pre &&
            n == string_length(input) &&
            i == n &&
            out != 0 &&
            nletter == n &&
            w == w &&
            no_letter_z_161(input) &&
            flip_output_z_161(input, output) &&
            valid_string(input) &&
            valid_string(output) &&
            problem_161_pre_z(input) &&
            ascii_range_z(input) &&
            string_length(input) < INT_MAX &&
            store_string(s@pre, input) *
            CharArray::full(out, n + 1, c_string(output))
        */
        char *p = malloc_char_array(n + 1);
        if (p == 0) return 0;

        int j;
        /*@ Inv Assert exists output rev_output,
            s == s@pre &&
            n == string_length(input) &&
            i == n &&
            out != 0 && p != 0 &&
            nletter == n &&
            w == w &&
            0 <= j && j <= n &&
            no_letter_z_161(input) &&
            flip_output_z_161(input, output) &&
            reverse_scan_state_z_161(input, rev_output, j) &&
            valid_string(input) &&
            valid_string(output) &&
            problem_161_pre_z(input) &&
            ascii_range_z(input) &&
            string_length(input) < INT_MAX &&
            store_string(s@pre, input) *
            CharArray::full(out, n + 1, c_string(output)) *
            CharArray::full(p, j, rev_output) *
            CharArray::undef_seg(p, j, n + 1)
        */
        for (j = 0; j < n; j++) {
            p[j] = s[n - 1 - j];
            /*@ Assert exists output rev_output,
                s == s@pre &&
                n == string_length(input) &&
                i == n &&
                out != 0 && p != 0 &&
                nletter == n &&
                w == w &&
                0 <= j && j < n &&
                no_letter_z_161(input) &&
                flip_output_z_161(input, output) &&
                reverse_scan_state_z_161(input, rev_output, j + 1) &&
                valid_string(input) &&
                valid_string(output) &&
                problem_161_pre_z(input) &&
                ascii_range_z(input) &&
                string_length(input) < INT_MAX &&
                store_string(s@pre, input) *
                CharArray::full(out, n + 1, c_string(output)) *
                CharArray::full(p, j + 1, rev_output) *
                CharArray::undef_seg(p, j + 1, n + 1)
            */
        }
        /*@ Assert exists output rev_output,
            s == s@pre &&
            n == string_length(input) &&
            i == n && j == n &&
            out != 0 && p != 0 &&
            nletter == n &&
            w == w &&
            no_letter_z_161(input) &&
            flip_output_z_161(input, output) &&
            reverse_output_z_161(input, rev_output) &&
            valid_string(input) &&
            valid_string(output) &&
            valid_string(rev_output) &&
            problem_161_pre_z(input) &&
            problem_161_spec_z(input, rev_output) &&
            ascii_range_z(input) &&
            string_length(input) < INT_MAX &&
            store_string(s@pre, input) *
            CharArray::full(out, n + 1, c_string(output)) *
            CharArray::full(p, n, rev_output) *
            CharArray::undef_seg(p, n, n + 1)
        */
        p[n] = 0;
        free_char_array(out, n + 1);
        return p;
    }

    /*@ Assert exists output,
        s == s@pre &&
        n == string_length(input) &&
        i == n &&
        out != 0 &&
        nletter != n &&
        w == w &&
        has_letter_z_161(input) &&
        flip_output_z_161(input, output) &&
        valid_string(input) &&
        valid_string(output) &&
        problem_161_pre_z(input) &&
        problem_161_spec_z(input, output) &&
        ascii_range_z(input) &&
        string_length(input) < INT_MAX &&
        store_string(s@pre, input) *
        CharArray::full(out, n + 1, c_string(output))
    */
    return out;
}
