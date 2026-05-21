#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_89_pre_z: list Z -> Prop)
               (problem_89_spec_z: list Z -> list Z -> Prop)
               (encrypt_char_z: Z -> Z)
               (ascii_range_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_89 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

char *encrypt(char *s)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_89_pre_z(l) &&
            ascii_range_z(l) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
            Zlength(out_l) == len &&
            problem_89_spec_z(l, out_l) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(s) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 1);

    /*@ Inv Assert
        exists out_l,
        s == s@pre &&
        n == len &&
        Zlength(l) == len &&
        problem_89_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n &&
        Zlength(out_l) == i &&
        (forall (k: Z), (0 <= k && k < i) =>
            Znth(k, out_l, 0) == encrypt_char_z(Znth(k, l, 0))) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, i, out_l) *
        CharArray::undef_seg(out, i, n + 1)
    */
    for (i = 0; i < n; i++) {
        int w = (s[i] + 4 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
