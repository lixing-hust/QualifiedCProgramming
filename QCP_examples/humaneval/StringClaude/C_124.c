/*
You have to write a function which validates a given date string &&
returns true if the date is valid otherwise false.
The date is valid if all of the following rules are satisfied:
1. The date string is ! empty.
2. The number of days is ! less than 1 || higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is ! less than 1 || higher than 30 days for months 4,6,9,11. And, the number of days is ! less than 1 || higher than 29 for the month 2.
3. The months should ! be less than 1 || higher than 12.
4. The date should be in the format: mm-dd-yyyy

for example:
valid_date("03-11-2000") => true

valid_date("15-01-2012") => false

valid_date("04-0-2040") => false

valid_date("06-04-2020") => true

valid_date("06/04/2020") => false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_124_pre_z: list Z -> Prop)
               (problem_124_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (date_prefix_valid: Z -> list Z -> Prop)
               (valid_date_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_124 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int valid_date(char *date)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_124_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(date, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_124_spec_z(l, __return) &&
        CharArray::full(date, len + 1, app(l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(date) /*@ where l = l, n = len */;
    if (n != 10) {
        return 0;
    }
    /*@ Inv Assert
        date == date@pre &&
        n == 10 &&
        len == 10 &&
        Zlength(l) == 10 &&
        problem_124_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= 10 &&
        date_prefix_valid(i, l) &&
        CharArray::full(date, len + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < 10; i++) {
        if (i == 2 || i == 5) {
            if (date[i] != 45) {
                return 0;
            }
        } else {
            if (date[i] < 48 || date[i] > 57) {
                return 0;
            }
        }
    }

    int mm = (date[0] - 48) * 10 + (date[1] - 48);
    int dd = (date[3] - 48) * 10 + (date[4] - 48);
    if (mm < 1 || mm > 12) {
        return 0;
    }
    if (dd < 1 || dd > 31) {
        return 0;
    }
    if (dd == 31 && (mm == 4 || mm == 6 || mm == 9 || mm == 11 || mm == 2)) {
        return 0;
    }
    if (dd == 30 && mm == 2) {
        return 0;
    }
    return 1;
}
