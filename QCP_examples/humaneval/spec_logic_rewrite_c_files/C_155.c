/*
Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    even_odd_count(-12) ==> {1, 1}
    even_odd_count(123) ==> {1, 2}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs_155: Z -> Z)
               (problem_155_pre_z: Z -> Prop)
               (problem_155_spec_z: Z -> list Z -> Prop)
               (even_odd_safe_155: Z -> Prop)
               (digit_count_state_155: Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_155 */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require
        size > 0 && size < INT_MAX
    Ensure
        __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *even_odd_count(int num)
/*@ With (num0: Z)
    Require
        num == num0 &&
        INT_MIN < num0 && num0 <= INT_MAX &&
        problem_155_pre_z(num0) &&
        even_odd_safe_155(num0) && emp
    Ensure
        exists data even odd,
        __return != 0 &&
        data != 0 &&
        problem_155_spec_z(num0, cons(even, cons(odd, nil))) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), 2) *
        IntArray::full(data, 2, cons(even, cons(odd, nil)))
*/
{
    int w;
    if (num < 0) {
        w = -num;
    } else {
        w = num;
    }
    int n1=0,n2=0;
    int d = 0;
    if (w == 0) {
        n2 = 1;
    }
    /*@ Inv Assert
        num == num0 &&
        INT_MIN < num0 && num0 <= INT_MAX &&
        problem_155_pre_z(num0) &&
        even_odd_safe_155(num0) &&
        0 <= w && w <= Zabs_155(num0) &&
        0 <= n1 && n1 <= Zabs_155(num0) + 1 &&
        0 <= n2 && n2 <= Zabs_155(num0) + 1 &&
        digit_count_state_155(num0, w, n2, n1) &&
        data_at(&d, d)
    */
    while (w > 0) {
        d = w % 10;
        if (d % 2 == 1) {
            n1 += 1;
        } else {
            n2 += 1;
        }
        w /= 10;
        /*@ Assert
            num == num0 &&
            INT_MIN < num0 && num0 <= INT_MAX &&
            problem_155_pre_z(num0) &&
            even_odd_safe_155(num0) &&
            0 <= w && w <= Zabs_155(num0) &&
            0 <= n1 && n1 <= Zabs_155(num0) + 1 &&
            0 <= n2 && n2 <= Zabs_155(num0) + 1 &&
            digit_count_state_155(num0, w, n2, n1) &&
            data_at(&d, d)
        */
    }
    IntArray *out = malloc_int_array_struct();
    int *data = malloc_int_array(2);
    out->data = data;
    out->size = 2;
    data[0] = n2;
    data[1] = n1;
    /*@ Assert
        num == num0 &&
        problem_155_pre_z(num0) &&
        even_odd_safe_155(num0) &&
        digit_count_state_155(num0, 0, n2, n1) &&
        problem_155_spec_z(num0, cons(n2, cons(n1, nil))) &&
        out != 0 &&
        data != 0 &&
        data_at(&w, 0) *
        data_at(&d, d) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 2) *
        IntArray::full(data, 2, cons(n2, cons(n1, nil)))
    */
    return out;
}
