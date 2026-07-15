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
               (collatz_safe_123: Z -> Prop)
               (collatz_count_state_123: Z -> Z -> Z -> Prop)
               (collatz_final_count_123: Z -> Z -> Prop)
               (collatz_output_state_123: Z -> Z -> Z -> list Z -> Prop)
               (collatz_next_123: Z -> Z)
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
/*@ Require size > 0 && size < INT_MAX
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

IntArray *get_odd_collatz(int n)
/*@ With n0
    Require
        n == n0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0)
    Ensure
        exists data output_l data_l output_size data_cap,
        __return != 0 &&
        data != 0 &&
        0 < output_size && output_size < INT_MAX &&
        output_size < data_cap && data_cap < INT_MAX &&
        output_size == Zlength(output_l) &&
        data_cap == Zlength(data_l) &&
        sublist(0, output_size, data_l) == output_l &&
        problem_123_spec_z(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, data_cap, data_l)
*/
{
    int cur = n;
    int count = 1;

    /*@ Inv Assert
        n == n0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0) &&
        0 < cur && cur < INT_MAX &&
        0 < count && count < INT_MAX &&
        collatz_count_state_123(n0, cur, count)
    */
    while (cur != 1) {
        if (cur % 2 == 1) {
            count = count + 1;
            cur = 3 * cur + 1;
        } else {
            cur = cur / 2;
        }
    }

    cur = n;

    /*@ Assert
        n == n0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0) &&
        collatz_final_count_123(n0, count) &&
        0 < count && count + 1 < INT_MAX &&
        data_at(&cur, n0)
    */
    IntArray *out = malloc_int_array_struct();
    int cap = count + 1;
    int *data = malloc_int_array(cap);
    data[0] = 1;
    int size = 1;

    /*@ Inv Assert
        exists output_l,
        n == n0 &&
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0) &&
        collatz_final_count_123(n0, count) &&
        cap == count + 1 &&
        0 < cur && cur < INT_MAX &&
        0 < count && count + 1 < INT_MAX &&
        1 <= size && size <= count &&
        size == Zlength(output_l) &&
        collatz_output_state_123(n0, count, cur, output_l) &&
        IntArray::seg(data, 0, size, output_l) *
        IntArray::undef_seg(data, size, cap) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size))
    */
    while (cur != 1) {
        if (cur % 2 == 1) {
            data[size] = cur;
            size = size + 1;
            cur = 3 * cur + 1;
        } else {
            cur = cur / 2;
        }
    }

    /*@ Assert
        exists output_l,
        n == n0 &&
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0) &&
        collatz_final_count_123(n0, count) &&
        cap == count + 1 &&
        size == count &&
        size == Zlength(output_l) &&
        collatz_output_state_123(n0, count, 1, output_l) &&
        IntArray::seg(data, 0, size, output_l) *
        IntArray::undef_seg(data, size, cap) *
        data_at(&cur, 1) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size))
    */
    sort_int_array(data, size, cap, 1);

    /*@ Assert
        exists output_l sorted_l data_l,
        n == n0 &&
        out != 0 &&
        data != 0 &&
        problem_123_pre_z(n0) &&
        collatz_safe_123(n0) &&
        collatz_final_count_123(n0, count) &&
        cap == count + 1 &&
        size == count &&
        size == Zlength(output_l) &&
        size == Zlength(sorted_l) &&
        cap == Zlength(data_l) &&
        sublist(0, size, data_l) == sorted_l &&
        collatz_output_state_123(n0, count, 1, output_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(output_l, sorted_l) &&
        problem_123_spec_z(n0, sorted_l) &&
        IntArray::full(data, cap, data_l) *
        data_at(&cur, 1) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size))
    */
    out->data = data;
    out->size = size;
    /*@ Assert
        exists output_l data_l,
        n == n0 &&
        out != 0 &&
        data != 0 &&
        problem_123_spec_z(n0, output_l) &&
        0 < size && size < cap && cap < INT_MAX &&
        size == Zlength(output_l) &&
        cap == Zlength(data_l) &&
        sublist(0, size, data_l) == output_l &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), size) *
        IntArray::full(data, cap, data_l) *
        data_at(&cur, 1) *
        data_at(&count, count)
    */
    return out;
}
