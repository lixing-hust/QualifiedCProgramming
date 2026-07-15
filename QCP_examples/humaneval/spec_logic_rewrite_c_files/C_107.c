/*
Given a positive integer n, return a vector that has the number of even && odd
integer palindromes that fall within the range(1, n), inclusive.

Example 1:

    Input: 3
    Output: (1, 2)
    Explanation:
    Integer palindrome are 1, 2, 3. one of them is even, && two of them are odd.

Example 2:

    Input: 12
    Output: (4, 6)
    Explanation:
    Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, && 6 of them are odd.

Note:
    1. 1 <= n <= 10^3
    2. returned vector has the number of even && odd integer palindromes respectively.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_107_pre_z: Z -> Prop)
               (problem_107_spec_z: Z -> list Z -> Prop)
               (is_pal_result_107: Z -> Z)
               (pal_scan_state_107: Z -> Z -> Z -> Prop)
               (count_even_pal_prefix_107: Z -> Z)
               (count_odd_pal_prefix_107: Z -> Z)
               (int_range_107: Z -> Prop) */
/*@ Import Coq Require Import coins_107 */

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

int is_pal(int x)
/*@ Require
        int_range_107(x) && emp
    Ensure
        __return == is_pal_result_107(x) && emp
*/
{
    int r = 0;
    int t = x;
    /*@ Inv Assert
        x == x@pre &&
        int_range_107(x) &&
        0 <= t && t <= x &&
        0 <= r && r <= 9999 &&
        pal_scan_state_107(x, t, r)
    */
    while (t > 0) {
        r = r * 10 + (t % 10);
        t /= 10;
    }
    return r == x;
}

IntArray *even_odd_palindrome(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        problem_107_pre_z(n0) &&
        int_range_107(n0) && emp
    Ensure
        exists data,
        __return != 0 &&
        data != 0 &&
        problem_107_spec_z(n0, cons(count_even_pal_prefix_107(n0),
                              cons(count_odd_pal_prefix_107(n0), nil))) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), 2) *
        IntArray::full(data, 2, cons(count_even_pal_prefix_107(n0),
                                cons(count_odd_pal_prefix_107(n0), nil)))
*/
{
    int num1=0,num2=0;
    IntArray *out = malloc_int_array_struct();
    int *data = malloc_int_array(2);
    int i;
    /*@ Inv Assert
        n == n0 &&
        problem_107_pre_z(n0) &&
        int_range_107(n0) &&
        1 <= i && i <= n + 1 &&
        0 <= num1 && num1 <= i - 1 &&
        0 <= num2 && num2 <= i - 1 &&
        num1 == count_odd_pal_prefix_107(i - 1) &&
        num2 == count_even_pal_prefix_107(i - 1) &&
        out != 0 &&
        data != 0 &&
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size)) *
        IntArray::undef_full(data, 2)
    */
    for (i=1;i<=n;i++)
    {
        if (is_pal(i) && i%2==1) num1+=1;
        if (is_pal(i) && i%2==0) num2+=1;
        /*@ Assert
            n == n0 &&
            problem_107_pre_z(n0) &&
            int_range_107(n0) &&
            1 <= i && i <= n &&
            0 <= num1 && num1 <= i &&
            0 <= num2 && num2 <= i &&
            num1 == count_odd_pal_prefix_107(i) &&
            num2 == count_even_pal_prefix_107(i) &&
            out != 0 &&
            data != 0 &&
            undef_data_at(&(out -> data)) *
            undef_data_at(&(out -> size)) *
            IntArray::undef_full(data, 2)
        */
    }
    /*@ Assert
        n == n0 &&
        problem_107_pre_z(n0) &&
        int_range_107(n0) &&
        num1 == count_odd_pal_prefix_107(n0) &&
        num2 == count_even_pal_prefix_107(n0) &&
        out != 0 &&
        data != 0 &&
        data_at(&i, n + 1) *
        undef_data_at(&(out -> data)) *
        undef_data_at(&(out -> size)) *
        IntArray::undef_full(data, 2)
    */
    out->data = data;
    out->size = 2;
    data[0] = num2;
    data[1] = num1;
    /*@ Assert
        n == n0 &&
        problem_107_pre_z(n0) &&
        int_range_107(n0) &&
        num1 == count_odd_pal_prefix_107(n0) &&
        num2 == count_even_pal_prefix_107(n0) &&
        out != 0 &&
        data != 0 &&
        data_at(&i, n + 1) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), 2) *
        IntArray::full(data, 2, cons(num2, cons(num1, nil)))
    */
    return out;
}
