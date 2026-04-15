/*
Input are two strings a && b consisting only of 1s && 0s.
Perform binary XOR on these inputs && return result also as a string.
>>> string_xor("010", "110")
"100"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_11_pre_z: list Z -> list Z -> Prop)
               (problem_11_spec_z: list Z -> list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_11 */

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

char *string_xor(char *a, char *b)
/*@ With l1 l2 na nb
    Require
        0 <= na && na < INT_MAX &&
        0 <= nb && nb < INT_MAX &&
        Zlength(l1) == na &&
        Zlength(l2) == nb &&
        na == nb &&
        problem_11_pre_z(l1, l2) &&
        CharArray::full(a, na + 1, app(l1, cons(0, nil))) *
        CharArray::full(b, nb + 1, app(l2, cons(0, nil)))
    Ensure exists out_l n,
        ((na <= nb && n == na) || (nb < na && n == nb)) &&
        Zlength(out_l) == n &&
        problem_11_spec_z(l1, l2, out_l) &&
        CharArray::full(a, na + 1, app(l1, cons(0, nil))) *
        CharArray::full(b, nb + 1, app(l2, cons(0, nil))) *
        CharArray::full(__return, n + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int n1 = strlen(a) /*@ where l = l1, n = na */;
    int n2 = strlen(b) /*@ where l = l2, n = nb */;
    int n;
    char *output;

    if (n1 < n2) {
        n = n1;
    } else {
        n = n2;
    }

    /*@ 0 <= n && n <= n1 && n <= n2 */
    output = malloc_char_array(n + 1);

    /*@ Inv Assert
        exists out_l,
        a == a@pre &&
        b == b@pre &&
        n1 == na &&
        n2 == nb &&
        Zlength(l1) == na &&
        Zlength(l2) == nb &&
        na == nb &&
        problem_11_pre_z(l1, l2) &&
        ((na <= nb && n == na) || (nb < na && n == nb)) &&
        0 <= i && i <= n &&
        n <= n1 && n <= n2 &&
        Zlength(out_l) == i &&
        CharArray::full(a, n1 + 1, app(l1, cons(0, nil))) *
        CharArray::full(b, n2 + 1, app(l2, cons(0, nil))) *
        CharArray::full(output, i, out_l) *
        CharArray::undef_seg(output, i, n + 1) &&
        (forall (k: Z), (0 <= k && k < i) =>
            ((Znth(k, l1, 0) == Znth(k, l2, 0) && Znth(k, out_l, 0) == 48) ||
             (Znth(k, l1, 0) != Znth(k, l2, 0) && Znth(k, out_l, 0) == 49)))
    */
    for (i = 0; i < n; i++) {
        if (a[i] == b[i]) {
            output[i] = 48;
        } else {
            output[i] = 49;
        }
    }
    output[n] = 0;
    return output;
}
