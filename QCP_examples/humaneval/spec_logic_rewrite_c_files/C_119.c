/*
You are given two strings consisting only of '(' and ')'.  Return Yes when
one of their two concatenation orders is balanced, and No otherwise.

The verification interface represents Yes by 1 and No by 0; coins_119.v
maps that representation directly back to the original string-valued spec.
*/
#include "verification_stdlib.h"
#include "string.h"

/*@ Extern Coq (problem_119_pre_z: list Z -> list Z -> Prop)
               (problem_119_spec_z: list Z -> list Z -> Z -> Prop)
               (paren_codes_119: list Z -> Prop)
               (paren_scan_state_119: list Z -> Z -> Z -> Z -> Prop)
               (string_length: list Z -> Z) */
/*@ Import Coq Require Import coins_119 */

int match_parens(char *s1, char *s2)
/*@ With l1 l2
    Require
        valid_string(l1) && valid_string(l2) &&
        problem_119_pre_z(l1, l2) &&
        paren_codes_119(l1) && paren_codes_119(l2) &&
        string_length(l1) + string_length(l2) < INT_MAX &&
        store_string(s1, l1) * store_string(s2, l2)
    Ensure
        problem_119_spec_z(l1, l2, __return) &&
        store_string(s1, l1) * store_string(s2, l2)
*/
{
    int n1 = strlen(s1) /*@ where str = l1 */;
    int n2 = strlen(s2) /*@ where str = l2 */;
    int i;
    int ch = 0;
    int count = 0;
    int can = 1;

    /*@ Inv Assert
        s1 == s1@pre && s2 == s2@pre &&
        n1 == string_length(l1) && n2 == string_length(l2) &&
        0 <= i && i <= n1 &&
        -i <= count && count <= i &&
        (can == 0 || can == 1) &&
        0 <= ch && ch <= 127 &&
        valid_string(l1) && valid_string(l2) &&
        problem_119_pre_z(l1, l2) &&
        paren_codes_119(l1) && paren_codes_119(l2) &&
        string_length(l1) + string_length(l2) < INT_MAX &&
        paren_scan_state_119(app(l1, l2), i, count, can) &&
        store_string(s1@pre, l1) * store_string(s2@pre, l2)
    */
    for (i = 0; i < n1; i++) {
        ch = s1[i];
        if (ch == 40) {
            count = count + 1;
        } else {
            count = count - 1;
        }
        if (count < 0) {
            can = 0;
        }
        /*@ Assert
            s1 == s1@pre && s2 == s2@pre &&
            n1 == string_length(l1) && n2 == string_length(l2) &&
            0 <= i && i < n1 &&
            -(i + 1) <= count && count <= i + 1 &&
            (can == 0 || can == 1) &&
            (ch == 40 || ch == 41) &&
            valid_string(l1) && valid_string(l2) &&
            problem_119_pre_z(l1, l2) &&
            paren_codes_119(l1) && paren_codes_119(l2) &&
            string_length(l1) + string_length(l2) < INT_MAX &&
            paren_scan_state_119(app(l1, l2), i + 1, count, can) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2)
        */
    }

    /*@ Inv Assert
        s1 == s1@pre && s2 == s2@pre &&
        n1 == string_length(l1) && n2 == string_length(l2) &&
        0 <= i && i <= n2 &&
        -(n1 + i) <= count && count <= n1 + i &&
        (can == 0 || can == 1) &&
        0 <= ch && ch <= 127 &&
        valid_string(l1) && valid_string(l2) &&
        problem_119_pre_z(l1, l2) &&
        paren_codes_119(l1) && paren_codes_119(l2) &&
        string_length(l1) + string_length(l2) < INT_MAX &&
        paren_scan_state_119(app(l1, l2), n1 + i, count, can) &&
        store_string(s1@pre, l1) * store_string(s2@pre, l2)
    */
    for (i = 0; i < n2; i++) {
        ch = s2[i];
        if (ch == 40) {
            count = count + 1;
        } else {
            count = count - 1;
        }
        if (count < 0) {
            can = 0;
        }
        /*@ Assert
            s1 == s1@pre && s2 == s2@pre &&
            n1 == string_length(l1) && n2 == string_length(l2) &&
            0 <= i && i < n2 &&
            -(n1 + i + 1) <= count && count <= n1 + i + 1 &&
            (can == 0 || can == 1) &&
            (ch == 40 || ch == 41) &&
            valid_string(l1) && valid_string(l2) &&
            problem_119_pre_z(l1, l2) &&
            paren_codes_119(l1) && paren_codes_119(l2) &&
            string_length(l1) + string_length(l2) < INT_MAX &&
            paren_scan_state_119(app(l1, l2), n1 + i + 1, count, can) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2)
        */
    }

    if (count != 0) {
        /*@ Assert
            problem_119_spec_z(l1, l2, 0) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2) *
            data_at(&s1, s1@pre) * data_at(&s2, s2@pre) *
            data_at(&n1, n1) * data_at(&n2, n2) *
            data_at(&i, i) * data_at(&ch, ch) *
            data_at(&count, count) * data_at(&can, can)
        */
        return 0;
    }
    if (can == 1) {
        /*@ Assert
            problem_119_spec_z(l1, l2, 1) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2) *
            data_at(&s1, s1@pre) * data_at(&s2, s2@pre) *
            data_at(&n1, n1) * data_at(&n2, n2) *
            data_at(&i, i) * data_at(&ch, ch) *
            data_at(&count, count) * data_at(&can, can)
        */
        return 1;
    }

    count = 0;
    can = 1;
    /*@ Inv Assert
        s1 == s1@pre && s2 == s2@pre &&
        n1 == string_length(l1) && n2 == string_length(l2) &&
        0 <= i && i <= n2 &&
        -i <= count && count <= i &&
        (can == 0 || can == 1) &&
        0 <= ch && ch <= 127 &&
        valid_string(l1) && valid_string(l2) &&
        problem_119_pre_z(l1, l2) &&
        paren_codes_119(l1) && paren_codes_119(l2) &&
        string_length(l1) + string_length(l2) < INT_MAX &&
        paren_scan_state_119(app(l1, l2), n1 + n2, 0, 0) &&
        paren_scan_state_119(app(l2, l1), i, count, can) &&
        store_string(s1@pre, l1) * store_string(s2@pre, l2)
    */
    for (i = 0; i < n2; i++) {
        ch = s2[i];
        if (ch == 40) {
            count = count + 1;
        } else {
            count = count - 1;
        }
        if (count < 0) {
            can = 0;
        }
        /*@ Assert
            s1 == s1@pre && s2 == s2@pre &&
            n1 == string_length(l1) && n2 == string_length(l2) &&
            0 <= i && i < n2 &&
            -(i + 1) <= count && count <= i + 1 &&
            (can == 0 || can == 1) &&
            (ch == 40 || ch == 41) &&
            valid_string(l1) && valid_string(l2) &&
            problem_119_pre_z(l1, l2) &&
            paren_codes_119(l1) && paren_codes_119(l2) &&
            string_length(l1) + string_length(l2) < INT_MAX &&
            paren_scan_state_119(app(l1, l2), n1 + n2, 0, 0) &&
            paren_scan_state_119(app(l2, l1), i + 1, count, can) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2)
        */
    }

    /*@ Inv Assert
        s1 == s1@pre && s2 == s2@pre &&
        n1 == string_length(l1) && n2 == string_length(l2) &&
        0 <= i && i <= n1 &&
        -(n2 + i) <= count && count <= n2 + i &&
        (can == 0 || can == 1) &&
        0 <= ch && ch <= 127 &&
        valid_string(l1) && valid_string(l2) &&
        problem_119_pre_z(l1, l2) &&
        paren_codes_119(l1) && paren_codes_119(l2) &&
        string_length(l1) + string_length(l2) < INT_MAX &&
        paren_scan_state_119(app(l1, l2), n1 + n2, 0, 0) &&
        paren_scan_state_119(app(l2, l1), n2 + i, count, can) &&
        store_string(s1@pre, l1) * store_string(s2@pre, l2)
    */
    for (i = 0; i < n1; i++) {
        ch = s1[i];
        if (ch == 40) {
            count = count + 1;
        } else {
            count = count - 1;
        }
        if (count < 0) {
            can = 0;
        }
        /*@ Assert
            s1 == s1@pre && s2 == s2@pre &&
            n1 == string_length(l1) && n2 == string_length(l2) &&
            0 <= i && i < n1 &&
            -(n2 + i + 1) <= count && count <= n2 + i + 1 &&
            (can == 0 || can == 1) &&
            (ch == 40 || ch == 41) &&
            valid_string(l1) && valid_string(l2) &&
            problem_119_pre_z(l1, l2) &&
            paren_codes_119(l1) && paren_codes_119(l2) &&
            string_length(l1) + string_length(l2) < INT_MAX &&
            paren_scan_state_119(app(l1, l2), n1 + n2, 0, 0) &&
            paren_scan_state_119(app(l2, l1), n2 + i + 1, count, can) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2)
        */
    }

    if (can == 1) {
        /*@ Assert
            problem_119_spec_z(l1, l2, 1) &&
            store_string(s1@pre, l1) * store_string(s2@pre, l2) *
            data_at(&s1, s1@pre) * data_at(&s2, s2@pre) *
            data_at(&n1, n1) * data_at(&n2, n2) *
            data_at(&i, i) * data_at(&ch, ch) *
            data_at(&count, count) * data_at(&can, can)
        */
        return 1;
    }
    /*@ Assert
        problem_119_spec_z(l1, l2, 0) &&
        store_string(s1@pre, l1) * store_string(s2@pre, l2) *
        data_at(&s1, s1@pre) * data_at(&s2, s2@pre) *
        data_at(&n1, n1) * data_at(&n2, n2) *
        data_at(&i, i) * data_at(&ch, ch) *
        data_at(&count, count) * data_at(&can, can)
    */
    return 0;
}
