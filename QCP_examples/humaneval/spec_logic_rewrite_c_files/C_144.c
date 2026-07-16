/*
Return true exactly when the product of two positive fractions is integral.
Both inputs have the form <positive decimal>/<positive decimal>.
*/
#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_144_pre_z: list Z -> list Z -> Prop)
               (problem_144_spec_z: list Z -> list Z -> Z -> Prop)
               (fraction_parts_z_144: list Z -> Z -> Z -> Z -> Prop)
               (fraction_scan_state_144:
                  list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_144 */

int simplify(char *x, char *n)
/*@ With lx ln (sx sy ax bx cn dn: Z)
    Require
        valid_string(lx) && valid_string(ln) &&
        string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
        problem_144_pre_z(lx, ln) &&
        fraction_parts_z_144(lx, sx, ax, bx) &&
        fraction_parts_z_144(ln, sy, cn, dn) &&
        1 <= ax && ax <= 46340 &&
        1 <= bx && bx <= 46340 &&
        1 <= cn && cn <= 46340 &&
        1 <= dn && dn <= 46340 &&
        store_string(x, lx) * store_string(n, ln)
    Ensure
        problem_144_spec_z(lx, ln, __return) &&
        store_string(x@pre, lx) * store_string(n@pre, ln)
*/
{
    int len_x = strlen(x) /*@ where str = lx */;
    int len_n = strlen(n) /*@ where str = ln */;
    int i;
    int ch = 0;
    int a = 0;
    int b = 0;
    int c = 0;
    int d = 0;
    int seen_x = 0;
    int seen_n = 0;

    /*@ Inv Assert
        x == x@pre && n == n@pre &&
        len_x == string_length(lx) && len_n == string_length(ln) &&
        0 <= i && i <= len_x &&
        0 <= ch && ch <= 127 &&
        0 <= a && a <= ax && 0 <= b && b <= bx &&
        (seen_x == 0 || seen_x == 1) &&
        c == 0 && d == 0 && seen_n == 0 &&
        valid_string(lx) && valid_string(ln) &&
        string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
        problem_144_pre_z(lx, ln) &&
        fraction_parts_z_144(lx, sx, ax, bx) &&
        fraction_parts_z_144(ln, sy, cn, dn) &&
        fraction_scan_state_144(lx, sx, ax, i, seen_x, a, b) &&
        1 <= ax && ax <= 46340 &&
        1 <= bx && bx <= 46340 &&
        1 <= cn && cn <= 46340 &&
        1 <= dn && dn <= 46340 &&
        store_string(x@pre, lx) * store_string(n@pre, ln)
    */
    for (i = 0; i < len_x; i++) {
        ch = x[i];
        if (ch == 47) {
            seen_x = 1;
        } else if (seen_x == 0) {
            a = a * 10 + (ch - 48);
        } else {
            b = b * 10 + (ch - 48);
        }
        /*@ Assert
            x == x@pre && n == n@pre &&
            len_x == string_length(lx) && len_n == string_length(ln) &&
            0 <= i && i < len_x &&
            0 <= ch && ch <= 127 &&
            0 <= a && a <= ax && 0 <= b && b <= bx &&
            (seen_x == 0 || seen_x == 1) &&
            c == 0 && d == 0 && seen_n == 0 &&
            valid_string(lx) && valid_string(ln) &&
            string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
            problem_144_pre_z(lx, ln) &&
            fraction_parts_z_144(lx, sx, ax, bx) &&
            fraction_parts_z_144(ln, sy, cn, dn) &&
            fraction_scan_state_144(lx, sx, ax, i + 1, seen_x, a, b) &&
            1 <= ax && ax <= 46340 &&
            1 <= bx && bx <= 46340 &&
            1 <= cn && cn <= 46340 &&
            1 <= dn && dn <= 46340 &&
            store_string(x@pre, lx) * store_string(n@pre, ln)
        */
    }

    /*@ Assert
        x == x@pre && n == n@pre &&
        len_x == string_length(lx) && len_n == string_length(ln) &&
        i == len_x && 0 <= ch && ch <= 127 &&
        a == ax && b == bx && seen_x == 1 &&
        c == 0 && d == 0 && seen_n == 0 &&
        valid_string(lx) && valid_string(ln) &&
        string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
        problem_144_pre_z(lx, ln) &&
        fraction_parts_z_144(lx, sx, ax, bx) &&
        fraction_parts_z_144(ln, sy, cn, dn) &&
        1 <= ax && ax <= 46340 &&
        1 <= bx && bx <= 46340 &&
        1 <= cn && cn <= 46340 &&
        1 <= dn && dn <= 46340 &&
        store_string(x@pre, lx) * store_string(n@pre, ln)
    */

    /*@ Inv Assert
        x == x@pre && n == n@pre &&
        len_x == string_length(lx) && len_n == string_length(ln) &&
        0 <= i && i <= len_n &&
        0 <= ch && ch <= 127 &&
        a == ax && b == bx && seen_x == 1 &&
        0 <= c && c <= cn && 0 <= d && d <= dn &&
        (seen_n == 0 || seen_n == 1) &&
        valid_string(lx) && valid_string(ln) &&
        string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
        problem_144_pre_z(lx, ln) &&
        fraction_parts_z_144(lx, sx, ax, bx) &&
        fraction_parts_z_144(ln, sy, cn, dn) &&
        fraction_scan_state_144(ln, sy, cn, i, seen_n, c, d) &&
        1 <= ax && ax <= 46340 &&
        1 <= bx && bx <= 46340 &&
        1 <= cn && cn <= 46340 &&
        1 <= dn && dn <= 46340 &&
        store_string(x@pre, lx) * store_string(n@pre, ln)
    */
    for (i = 0; i < len_n; i++) {
        ch = n[i];
        if (ch == 47) {
            seen_n = 1;
        } else if (seen_n == 0) {
            c = c * 10 + (ch - 48);
        } else {
            d = d * 10 + (ch - 48);
        }
        /*@ Assert
            x == x@pre && n == n@pre &&
            len_x == string_length(lx) && len_n == string_length(ln) &&
            0 <= i && i < len_n &&
            0 <= ch && ch <= 127 &&
            a == ax && b == bx && seen_x == 1 &&
            0 <= c && c <= cn && 0 <= d && d <= dn &&
            (seen_n == 0 || seen_n == 1) &&
            valid_string(lx) && valid_string(ln) &&
            string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
            problem_144_pre_z(lx, ln) &&
            fraction_parts_z_144(lx, sx, ax, bx) &&
            fraction_parts_z_144(ln, sy, cn, dn) &&
            fraction_scan_state_144(ln, sy, cn, i + 1, seen_n, c, d) &&
            1 <= ax && ax <= 46340 &&
            1 <= bx && bx <= 46340 &&
            1 <= cn && cn <= 46340 &&
            1 <= dn && dn <= 46340 &&
            store_string(x@pre, lx) * store_string(n@pre, ln)
        */
    }

    /*@ Assert
        x == x@pre && n == n@pre &&
        len_x == string_length(lx) && len_n == string_length(ln) &&
        i == len_n && 0 <= ch && ch <= 127 &&
        a == ax && b == bx && c == cn && d == dn &&
        seen_x == 1 && seen_n == 1 &&
        valid_string(lx) && valid_string(ln) &&
        string_length(lx) < INT_MAX && string_length(ln) < INT_MAX &&
        problem_144_pre_z(lx, ln) &&
        fraction_parts_z_144(lx, sx, ax, bx) &&
        fraction_parts_z_144(ln, sy, cn, dn) &&
        1 <= ax && ax <= 46340 &&
        1 <= bx && bx <= 46340 &&
        1 <= cn && cn <= 46340 &&
        1 <= dn && dn <= 46340 &&
        store_string(x@pre, lx) * store_string(n@pre, ln)
    */
    if ((a * c) % (b * d) == 0) {
        return 1;
    }
    return 0;
}
