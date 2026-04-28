/*
Given a positive integer n, return a sorted vector that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
    1. Collatz(1) is {1}.
    2. returned vector sorted in increasing order.

For example:
get_odd_collatz(5) returns {1, 5} // The collatz sequence for 5 is {5, 16, 8, 4, 2, 1}, so the odd numbers are only 1, && 5.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_123_pre_z: Z -> Prop)
               (problem_123_spec_z: Z -> list Z -> Prop)
               (odd_collatz_prefix: Z -> Z -> list Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_123 */

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

void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require
        array != 0 &&
        init_size == Zlength(l) &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        exists sorted_l sorted_full_l,
        init_size == Zlength(sorted_l) &&
        size == Zlength(sorted_full_l) &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        sublist(0, init_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, sorted_full_l)
*/;

int append_int(int *data, int output_size, int value)
/*@ With l
    Require
        data != 0 &&
        0 <= output_size && output_size < 1024 &&
        INT_MIN <= value && value <= INT_MAX &&
        output_size == Zlength(l) &&
        IntArray::seg(data, 0, output_size, l) *
        IntArray::undef_seg(data, output_size, 1024)
    Ensure
        exists new_l,
        __return == output_size + 1 &&
        __return == Zlength(new_l) &&
        new_l == app(l, cons(value, nil)) &&
        IntArray::seg(data, 0, __return, new_l) *
        IntArray::undef_seg(data, __return, 1024)
*/
{
    data[output_size] = value;
    return output_size + 1;
}

IntArray *get_odd_collatz(int n)
/*@ Require
        problem_123_pre_z(n)
    Ensure
        exists data output_l output_size data_l,
        __return != 0 &&
        data != 0 &&
        0 < output_size && output_size <= 1024 &&
        output_size == Zlength(output_l) &&
        1024 == Zlength(data_l) &&
        sublist(0, output_size, data_l) == output_l &&
        problem_123_spec_z(n, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, 1024, data_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(1024);
    int *data = out->data;
    int output_size = 0;

    data[output_size] = 1;
    output_size = output_size + 1;

    /*@ Inv Assert
        exists output_l,
        n@pre == n@pre &&
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n@pre) &&
        0 < n && n < INT_MAX &&
        0 < output_size && output_size <= 1024 &&
        output_size == Zlength(output_l) &&
        odd_collatz_prefix(n@pre, n, output_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, 1024)
    */
    while (n != 1) {
        /*@ Assert
            exists output_l,
            n != 1 &&
            out != 0 &&
            data != 0 &&
            problem_123_pre_z(n@pre) &&
                0 < n && n <= INT_MAX && n < INT_MAX &&
                output_size < 1024 &&
            0 < n * 3 && n * 3 <= INT_MAX &&
            0 < n * 3 + 1 && n * 3 + 1 < INT_MAX &&
            0 < output_size && output_size <= 1024 &&
            output_size == Zlength(output_l) &&
            odd_collatz_prefix(n@pre, n, output_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), 0) *
            IntArray::seg(data, 0, output_size, output_l) *
            IntArray::undef_seg(data, output_size, 1024)
        */
        if (n % 2 == 1) {
            /*@ Assert
                exists output_l,
                n != 1 &&
                n % 2 == 1 &&
                out != 0 &&
                data != 0 &&
                problem_123_pre_z(n@pre) &&
                INT_MIN <= n && 0 < n && n <= INT_MAX && n < INT_MAX &&
                output_size < 1024 &&
                0 < output_size && output_size <= 1024 &&
                output_size == Zlength(output_l) &&
                odd_collatz_prefix(n@pre, n, output_l) &&
                data_at(&(out -> data), data) *
                data_at(&(out -> size), 0) *
                IntArray::seg(data, 0, output_size, output_l) *
                IntArray::undef_seg(data, output_size, 1024)
            */
            output_size = append_int(data, output_size, n);
            n = n * 3 + 1;
        } else {
            n = n / 2;
        }
    }

    /*@ Assert
        exists output_l,
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n@pre) &&
        0 < output_size && output_size <= 1024 &&
        output_size == Zlength(output_l) &&
        odd_collatz_prefix(n@pre, 1, output_l) &&
        data_at(&n, 1) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, 1024)
    */
    sort_int_array(data, output_size, 1024, 1);

    /*@ Assert
        exists output_l sorted_l data_l,
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n@pre) &&
        0 < output_size && output_size <= 1024 &&
        output_size == Zlength(output_l) &&
        output_size == Zlength(sorted_l) &&
        1024 == Zlength(data_l) &&
        sublist(0, output_size, data_l) == sorted_l &&
        odd_collatz_prefix(n@pre, 1, output_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(output_l, sorted_l) &&
        problem_123_spec_z(n@pre, sorted_l) &&
        data_at(&n, 1) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 0) *
        IntArray::full(data, 1024, data_l)
    */
    out->size = output_size;
    return out;
}
