/*
Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    even_odd_count(-12) ==> {1, 1}
    even_odd_count(123) ==> {1, 2}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_155_pre_z: Z -> Prop)
               (problem_155_spec_z: Z -> list Z -> Prop)
               (digit_count_state: Z -> Z -> Z -> Z -> Prop) */
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
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

IntArray *even_odd_count(int num)
/*@ Require
        INT_MIN < num && num < INT_MAX &&
        Zabs(num) + 1 < INT_MAX &&
        problem_155_pre_z(num)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == 2 &&
        output_size == Zlength(output_l) &&
        problem_155_spec_z(num, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    int w = abs(num);
    int n1=0,n2=0;
    int d=0;
    if (w == 0) n2 = 1;
    /*@ Inv Assert
        num == num@pre &&
        INT_MIN < num@pre && num@pre < INT_MAX &&
        Zabs(num@pre) + 1 < INT_MAX &&
        problem_155_pre_z(num@pre) &&
        0 <= w && w <= INT_MAX &&
        0 <= n1 && n1 < INT_MAX &&
        0 <= n2 && n2 < INT_MAX &&
        digit_count_state(num@pre, w, n2, n1) &&
        data_at(&d, d)
    */
    while (w > 0) {
        d = w % 10;
        if (d % 2 == 1) {
            n1 += 1;
            /*@ Assert
                num == num@pre &&
                INT_MIN < num@pre && num@pre < INT_MAX &&
                Zabs(num@pre) + 1 < INT_MAX &&
                problem_155_pre_z(num@pre) &&
                0 < w && w <= INT_MAX &&
                d == w % 10 &&
                0 <= n1 && n1 < INT_MAX &&
                0 <= n2 && n2 < INT_MAX &&
                digit_count_state(num@pre, w / 10, n2, n1)
            */
        } else {
            n2 += 1;
            /*@ Assert
                num == num@pre &&
                INT_MIN < num@pre && num@pre < INT_MAX &&
                Zabs(num@pre) + 1 < INT_MAX &&
                problem_155_pre_z(num@pre) &&
                0 < w && w <= INT_MAX &&
                d == w % 10 &&
                0 <= n1 && n1 < INT_MAX &&
                0 <= n2 && n2 < INT_MAX &&
                digit_count_state(num@pre, w / 10, n2, n1)
            */
        }
        w /= 10;
    }
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = n2;
    data[1] = n1;
    return out;
}
