/*
The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fibfib(0) == 0
fibfib(1) == 0
fibfib(2) == 1
fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
Please write a function to efficiently compute the n-th element of the fibfib number sequence.
>>> fibfib(1)
0
>>> fibfib(5)
4
>>> fibfib(8)
24
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_63_pre_z: Z -> Prop)
               (problem_63_spec_z: Z -> Z -> Prop)
               (fibfib_z: Z -> Z)
               (fibfib_prefix_z: Z -> list Z)
               (fibfib_fill_len_z: Z -> Z -> Z)
               (fibfib_safe_z: Z -> Prop) */
/*@ Import Coq Require Import coins_63 */

int *malloc_int_array(int size)
/*@ Require
        size == 100 && emp
    Ensure
        __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int init_size, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= init_size && init_size <= size &&
        size == 100 &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        emp
*/;

int fibfib(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) && emp
    Ensure
        problem_63_spec_z(n0, __return) && emp
*/
{
    int *ff = malloc_int_array(100);
    ff[0]=0;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        IntArray::seg(ff, 0, 1, cons(0, nil)) *
        IntArray::undef_seg(ff, 1, 100)
    */
    ff[1]=0;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        IntArray::seg(ff, 0, 2, cons(0, cons(0, nil))) *
        IntArray::undef_seg(ff, 2, 100)
    */
    ff[2]=1;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        IntArray::seg(ff, 0, 3, fibfib_prefix_z(3)) *
        IntArray::undef_seg(ff, 3, 100)
    */
    /*@ Inv Assert
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        3 <= i && i <= 39 &&
        (n0 < 3 && i == 3 || 3 <= n0 && i <= n0 + 1) &&
        IntArray::seg(ff, 0, fibfib_fill_len_z(n0, i), fibfib_prefix_z(fibfib_fill_len_z(n0, i))) *
        IntArray::undef_seg(ff, fibfib_fill_len_z(n0, i), 100)
    */
    for (int i=3;i<=n;i++)
    {
        /*@ Assert
            n == n0 &&
            0 <= n0 && n0 <= 38 &&
            problem_63_pre_z(n0) &&
            fibfib_safe_z(n0) &&
            ff != 0 &&
            3 <= i && i <= n0 &&
            fibfib_fill_len_z(n0, i) == i &&
            IntArray::seg(ff, 0, i, fibfib_prefix_z(i)) *
            IntArray::undef_seg(ff, i, 100)
        */
        int a = ff[i-1];
        int b = ff[i-2];
        int c = ff[i-3];
        ff[i]=a+b+c;
        /*@ Assert
            n == n0 &&
            0 <= n0 && n0 <= 38 &&
            problem_63_pre_z(n0) &&
            fibfib_safe_z(n0) &&
            ff != 0 &&
            3 <= i && i <= n0 &&
            a == fibfib_z(i - 1) &&
            b == fibfib_z(i - 2) &&
            c == fibfib_z(i - 3) &&
            0 <= a + b && a + b <= INT_MAX &&
            fibfib_z(i) == a + b + c &&
            IntArray::seg(ff, 0, i + 1, fibfib_prefix_z(i + 1)) *
            IntArray::undef_seg(ff, i + 1, 100)
        */
    }
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        IntArray::seg(ff, 0, fibfib_fill_len_z(n0, n0 + 1), fibfib_prefix_z(fibfib_fill_len_z(n0, n0 + 1))) *
        IntArray::undef_seg(ff, fibfib_fill_len_z(n0, n0 + 1), 100)
    */
    int filled = n + 1;
    if (n < 3) {
        filled = 3;
    }
    /*@ Assert
        n == n0 &&
        filled == fibfib_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        filled <= 100 &&
        IntArray::seg(ff, 0, filled, fibfib_prefix_z(filled)) *
        IntArray::undef_seg(ff, filled, 100)
    */
    int result = ff[n];
    /*@ Assert
        n == n0 &&
        result == fibfib_z(n0) &&
        filled == fibfib_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 38 &&
        problem_63_pre_z(n0) &&
        fibfib_safe_z(n0) &&
        ff != 0 &&
        filled <= 100 &&
        IntArray::seg(ff, 0, filled, fibfib_prefix_z(filled)) *
        IntArray::undef_seg(ff, filled, 100)
    */
    free_int_array(ff, filled, 100);
    return result;
}
