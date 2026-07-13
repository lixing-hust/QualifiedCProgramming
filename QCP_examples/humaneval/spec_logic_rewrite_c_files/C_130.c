/*
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
tri(1) = 3
tri(n) = 1 + n / 2, if n is even.
tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
For example:
tri(2) = 1 + (2 / 2) = 2
tri(4) = 3
tri(3) = tri(2) + tri(1) + tri(4)
       = 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a vector of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
tri(3) = {1, 3, 2, 8}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_130_pre_z: Z -> Prop)
               (problem_130_spec_z: Z -> list Z -> Prop)
               (tri_z_130: Z -> Z)
               (tri_prefix_z_130: Z -> list Z)
               (tri_safe_z_130: Z -> Prop) */
/*@ Import Coq Require Import coins_130 */

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

IntArray *tri(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        0 <= n0 && n0 <= 1000 &&
        problem_130_pre_z(n0) &&
        tri_safe_z_130(n0) && emp
    Ensure
        exists data,
        __return != 0 &&
        data != 0 &&
        problem_130_spec_z(n0, tri_prefix_z_130(n0 + 1)) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), n0 + 1) *
        IntArray::full(data, n0 + 1, tri_prefix_z_130(n0 + 1))
*/
{
    IntArray *out = malloc_int_array_struct();
    int size = n + 1;
    int *data = malloc_int_array(size);
    out->size = size;
    out->data = data;
    data[0] = 1;
    /*@ Assert
        n == n0 &&
        size == n0 + 1 &&
        0 <= n0 && n0 <= 1000 &&
        problem_130_pre_z(n0) &&
        tri_safe_z_130(n0) &&
        out != 0 &&
        data != 0 &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), size) *
        IntArray::seg(data, 0, 1, tri_prefix_z_130(1)) *
        IntArray::undef_seg(data, 1, size)
    */
    if (n==0) {
        /*@ Assert
            n == n0 &&
            n0 == 0 &&
            size == n0 + 1 &&
            problem_130_pre_z(n0) &&
            tri_safe_z_130(n0) &&
            out != 0 &&
            data != 0 &&
            problem_130_spec_z(n0, tri_prefix_z_130(n0 + 1)) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), n0 + 1) *
            IntArray::full(data, n0 + 1, tri_prefix_z_130(n0 + 1))
        */
        return out;
    }
    data[1] = 3;
    /*@ Inv Assert
        n == n0 &&
        size == n0 + 1 &&
        1 <= n0 && n0 <= 1000 &&
        problem_130_pre_z(n0) &&
        tri_safe_z_130(n0) &&
        2 <= i && i <= n0 + 1 &&
        out != 0 &&
        data != 0 &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), size) *
        IntArray::seg(data, 0, i, tri_prefix_z_130(i)) *
        IntArray::undef_seg(data, i, size)
    */
    for (int i=2;i<=n;i++)
    {
        if (i%2==0) {
            data[i] = 1+i/2;
        } else {
            data[i] = data[i-1]+data[i-2]+1+(i+1)/2;
        }
        /*@ Assert
            n == n0 &&
            size == n0 + 1 &&
            1 <= n0 && n0 <= 1000 &&
            problem_130_pre_z(n0) &&
            tri_safe_z_130(n0) &&
            2 <= i && i <= n0 &&
            out != 0 &&
            data != 0 &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), size) *
            IntArray::seg(data, 0, i + 1, tri_prefix_z_130(i + 1)) *
            IntArray::undef_seg(data, i + 1, size)
        */
    }
    /*@ Assert
        n == n0 &&
        size == n0 + 1 &&
        1 <= n0 && n0 <= 1000 &&
        problem_130_pre_z(n0) &&
        tri_safe_z_130(n0) &&
        out != 0 &&
        data != 0 &&
        problem_130_spec_z(n0, tri_prefix_z_130(n0 + 1)) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), n0 + 1) *
        IntArray::full(data, n0 + 1, tri_prefix_z_130(n0 + 1))
    */
    return out;
}
