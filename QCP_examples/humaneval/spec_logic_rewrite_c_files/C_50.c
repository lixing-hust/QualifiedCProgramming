#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_50_pre_z: list Z -> Prop)
               (problem_50_spec_z: list Z -> list Z -> Prop)
               (encode_prefix_50: list Z -> list Z -> Prop)
               (decode_prefix_50: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_50 */

char *malloc_char_array(int n)
/*@ Require 0 < n && n < INT_MAX
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char *encode_shift(char *s)
/*@ With l (s0: Z)
    Require s == s0 && problem_50_pre_z(l) && valid_string(l) &&
            string_length(l) + 1 < INT_MAX &&
            store_string(s, l)
    Ensure exists out_l,
             encode_prefix_50(l, out_l) &&
             Zlength(out_l) == string_length(l) &&
             store_string(s0, l) * store_string(__return, out_l)
*/
{
    int i;
    int n = strlen(s) /*@ where str = l */;
    char *out = malloc_char_array(n + 1);

    if (out == 0) {
        return 0;
    }

    /*@ Inv Assert
        exists out_l,
        s == s0 && problem_50_pre_z(l) && valid_string(l) &&
        n == string_length(l) &&
        0 <= i && i <= n &&
        Zlength(out_l) == i &&
        encode_prefix_50(l, out_l) &&
        store_string(s, l) *
        CharArray::full(out, i, out_l) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = (s[i] + 5 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}

char *decode_shift(char *s)
/*@ With l (s0: Z)
    Require s == s0 && problem_50_pre_z(l) && valid_string(l) &&
            string_length(l) + 1 < INT_MAX &&
            store_string(s, l)
    Ensure exists out_l,
             problem_50_spec_z(l, out_l) &&
             Zlength(out_l) == string_length(l) &&
             store_string(s0, l) * store_string(__return, out_l)
*/
{
    int i;
    int n = strlen(s) /*@ where str = l */;
    char *out = malloc_char_array(n + 1);

    if (out == 0) {
        return 0;
    }

    /*@ Inv Assert
        exists out_l,
        s == s0 && problem_50_pre_z(l) && valid_string(l) &&
        n == string_length(l) &&
        0 <= i && i <= n &&
        Zlength(out_l) == i &&
        decode_prefix_50(l, out_l) &&
        store_string(s, l) *
        CharArray::full(out, i, out_l) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = (s[i] + 21 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
