/*
Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
generate_integers(2, 8) => {2, 4, 6, 8}
generate_integers(8, 2) => {2, 4, 6, 8}
generate_integers(10, 14) => {}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_163_pre_z: Z -> Z -> Prop)
               (problem_163_spec_z: Z -> Z -> list Z -> Prop)
               (generate_prefix: Z -> Z -> Z -> list Z -> Prop)
               (generate_bounds: Z -> Z -> Z -> Z -> Prop)
               (z_min: Z -> Z -> Z)
               (z_max: Z -> Z -> Z) */
/*@ Import Coq Require Import coins_163 */

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

IntArray *generate_integers(int a,int b)
/*@ With (a0: Z) (b0: Z)
    Require
        a == a0 && b == b0 &&
        problem_163_pre_z(a0, b0) &&
        0 < a0 && a0 < INT_MAX &&
        0 < b0 && b0 < INT_MAX
    Ensure
        exists data output_l output_size capacity,
        __return != 0 &&
        data != 0 &&
        0 <= output_size && output_size <= capacity &&
        capacity == 10 &&
        problem_163_spec_z(a0, b0, output_l) &&
        output_size == Zlength(output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, 10)
*/
{
    int m = 0;
    IntArray *out = malloc_int_array_struct();
    out->data = (void *)0;
    out->size = 0;
    if (b<a)
    {
        m=a;a=b;b=m;
    }

    int capacity = 10;
    out->data = malloc_int_array(capacity);
    int *data = out->data;
    if (data == 0) {
        return out;
    }
    int output_size = out->size;
    int i;
    /*@ Inv Assert
        exists output_l,
        out != 0 &&
        data != 0 &&
        problem_163_pre_z(a0, b0) &&
        0 < a0 && a0 < INT_MAX &&
        0 < b0 && b0 < INT_MAX &&
        generate_bounds(a0, b0, a, b) &&
        capacity == 10 &&
        a <= i && i <= b + 1 &&
        0 <= output_size && output_size <= i - a &&
        generate_prefix(a, i, b, output_l) &&
        output_size == Zlength(output_l) &&
        data_at(&m, m) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, capacity)
    */
    for (i=a;i<=b;i++) {
        if (i<10 && i%2==0) {
            /*@ Assert
                exists output_l,
                out != 0 &&
                data != 0 &&
                problem_163_pre_z(a0, b0) &&
                0 < a0 && a0 < INT_MAX &&
                0 < b0 && b0 < INT_MAX &&
                generate_bounds(a0, b0, a, b) &&
                capacity == 10 &&
                a <= i && i <= b &&
                i < 10 &&
                i % 2 == 0 &&
                INT_MIN <= i && i <= INT_MAX &&
                0 <= output_size && output_size <= i - a &&
                output_size < 10 &&
                generate_prefix(a, i, b, output_l) &&
                output_size == Zlength(output_l) &&
                data_at(&m, m) *
                data_at(&(out -> data), data) *
                data_at(&(out -> size), 0) *
                IntArray::seg(data, 0, output_size, output_l) *
                IntArray::undef_seg(data, output_size, 10)
            */
            data[output_size] = i;
            output_size++;
            /*@ Assert
                exists output_l,
                out != 0 &&
                data != 0 &&
                problem_163_pre_z(a0, b0) &&
                0 < a0 && a0 < INT_MAX &&
                0 < b0 && b0 < INT_MAX &&
                generate_bounds(a0, b0, a, b) &&
                capacity == 10 &&
                a <= i && i <= b &&
                i < 10 &&
                i % 2 == 0 &&
                0 <= output_size && output_size <= i + 1 - a &&
                generate_prefix(a, i + 1, b, output_l) &&
                output_size == Zlength(output_l) &&
                data_at(&m, m) *
                data_at(&(out -> data), data) *
                data_at(&(out -> size), 0) *
                IntArray::seg(data, 0, output_size, output_l) *
                IntArray::undef_seg(data, output_size, 10)
            */
        }
        /*@ Assert
            exists output_l,
            out != 0 &&
            data != 0 &&
            problem_163_pre_z(a0, b0) &&
            0 < a0 && a0 < INT_MAX &&
            0 < b0 && b0 < INT_MAX &&
            generate_bounds(a0, b0, a, b) &&
            capacity == 10 &&
            a <= i && i <= b &&
            0 <= output_size && output_size <= i + 1 - a &&
            generate_prefix(a, i + 1, b, output_l) &&
            output_size == Zlength(output_l) &&
            data_at(&m, m) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), 0) *
            IntArray::seg(data, 0, output_size, output_l) *
            IntArray::undef_seg(data, output_size, 10)
        */
    }
    out->size = output_size;
    /*@ Assert
        exists output_l,
        out != 0 &&
        data != 0 &&
        problem_163_pre_z(a0, b0) &&
        0 < a0 && a0 < INT_MAX &&
        0 < b0 && b0 < INT_MAX &&
        generate_bounds(a0, b0, a, b) &&
        capacity == 10 &&
        i == b + 1 &&
        0 <= output_size && output_size <= 10 &&
        generate_prefix(a, b + 1, b, output_l) &&
        output_size == Zlength(output_l) &&
        data_at(&m, m) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, 10)
    */
    return out;
}
