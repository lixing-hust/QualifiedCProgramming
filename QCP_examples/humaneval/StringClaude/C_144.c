/*
Your task is to implement a function that will simplify the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

simplify("1/5", "5/1") = true
simplify("1/6", "2/1") = false
simplify("7/10", "10/2") = false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_144_pre_z: list Z -> list Z -> Prop)
               (problem_144_spec_z: list Z -> list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (fraction_parts_z: list Z -> Z -> Z -> Z -> Prop)
               (fraction_values_safe_z: Z -> Z -> Z -> Z -> Prop)
               (parse_digits_z: list Z -> Z) */
/*@ Import Coq Require Import coins_144 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int simplify(char *x, char *n)
/*@ With lx ln lenx lenn sx sn ax bx cn dn
    Require
        0 <= lenx && lenx < INT_MAX &&
        0 <= lenn && lenn < INT_MAX &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    Ensure
        problem_144_spec_z(lx, ln, __return) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
*/
{
    int a = 0;
    int b = 0;
    int c = 0;
    int d = 0;
    int i;

    int x_len = strlen(x) /*@ where l = lx, n = lenx */;

    /*@ Inv Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        0 <= i && i <= sx &&
        0 <= a && a <= ax &&
        b == 0 && c == 0 && d == 0 &&
        a == parse_digits_z(sublist(0, i, lx)) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    for (i = 0; x[i] != 47; i++) {
        a = a * 10 + (x[i] - 48);
    }

    /*@ Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        i == sx &&
        a == ax &&
        b == 0 && c == 0 && d == 0 &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    i = i + 1;

    /*@ Inv Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        sx + 1 <= i && i <= lenx &&
        a == ax &&
        0 <= b && b <= bx &&
        c == 0 && d == 0 &&
        b == parse_digits_z(sublist(sx + 1, i, lx)) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    for (; i < x_len; i++) {
        b = b * 10 + (x[i] - 48);
    }

    /*@ Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        i == lenx &&
        a == ax && b == bx &&
        c == 0 && d == 0 &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    int n_len = strlen(n) /*@ where l = ln, n = lenn */;

    /*@ Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        n_len == lenn &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        i == lenx &&
        a == ax && b == bx &&
        c == 0 && d == 0 &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */

    /*@ Inv Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        n_len == lenn &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        0 <= i && i <= sn &&
        a == ax && b == bx &&
        0 <= c && c <= cn &&
        d == 0 &&
        c == parse_digits_z(sublist(0, i, ln)) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    for (i = 0; n[i] != 47; i++) {
        c = c * 10 + (n[i] - 48);
    }

    /*@ Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        n_len == lenn &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        i == sn &&
        a == ax && b == bx &&
        c == cn && d == 0 &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    i = i + 1;

    /*@ Inv Assert
        x == x@pre &&
        n == n@pre &&
        x_len == lenx &&
        n_len == lenn &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre_z(lx, ln) &&
        ascii_range_z(lx) &&
        ascii_range_z(ln) &&
        fraction_parts_z(lx, sx, ax, bx) &&
        fraction_parts_z(ln, sn, cn, dn) &&
        fraction_values_safe_z(ax, bx, cn, dn) &&
        0 < sx && sx < lenx &&
        0 < sn && sn < lenn &&
        sn + 1 <= i && i <= lenn &&
        a == ax && b == bx && c == cn &&
        0 <= d && d <= dn &&
        d == parse_digits_z(sublist(sn + 1, i, ln)) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    */
    for (; i < n_len; i++) {
        d = d * 10 + (n[i] - 48);
    }

    int product_num = a * c;
    int product_den = b * d;
    if (product_num % product_den == 0) return 1;
    return 0;
}
