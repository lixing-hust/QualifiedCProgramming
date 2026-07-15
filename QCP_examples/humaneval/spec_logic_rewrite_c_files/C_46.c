/*
The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4(0) -> 0
fib4(1) -> 0
fib4(2) -> 2
fib4(3) -> 0
fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
Please write a function to efficiently compute the n-th element of the fib4 number sequence.  Do ! use recursion.
>>> fib4(5)
4
>>> fib4(6)
8
>>> fib4(7)
14
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_46_pre_z: Z -> Prop)
               (problem_46_spec_z: Z -> Z -> Prop)
               (fib4_z: Z -> Z)
               (fib4_prefix_z: Z -> list Z)
               (fib4_fill_len_z: Z -> Z -> Z)
               (fib4_safe_z: Z -> Prop) */
/*@ Import Coq Require Import coins_46 */

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

int fib4(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) && emp
    Ensure
        problem_46_spec_z(n0, __return) && emp
*/
{
    int *f = malloc_int_array(100);
    f[0]=0;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, 1, cons(0, nil)) *
        IntArray::undef_seg(f, 1, 100)
    */
    f[1]=0;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, 2, cons(0, cons(0, nil))) *
        IntArray::undef_seg(f, 2, 100)
    */
    f[2]=2;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, 3, cons(0, cons(0, cons(2, nil)))) *
        IntArray::undef_seg(f, 3, 100)
    */
    f[3]=0;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, 4, fib4_prefix_z(4)) *
        IntArray::undef_seg(f, 4, 100)
    */
    /*@ Inv Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        4 <= i && i <= 36 &&
        (n0 < 4 && i == 4 || 4 <= n0 && i <= n0 + 1) &&
        IntArray::seg(f, 0, fib4_fill_len_z(n0, i), fib4_prefix_z(fib4_fill_len_z(n0, i))) *
        IntArray::undef_seg(f, fib4_fill_len_z(n0, i), 100)
    */
    for (int i=4;i<=n;i++)
    {
        /*@ Assert
            n == n0 &&
            0 <= n0 && n0 <= 35 &&
            problem_46_pre_z(n0) &&
            fib4_safe_z(n0) &&
            f != 0 &&
            4 <= i && i <= n0 &&
            fib4_fill_len_z(n0, i) == i &&
            IntArray::seg(f, 0, i, fib4_prefix_z(i)) *
            IntArray::undef_seg(f, i, 100)
        */
        int a = f[i-1];
        int b = f[i-2];
        int c = f[i-3];
        int d = f[i-4];
        f[i]=a+b+c+d;
        /*@ Assert
            n == n0 &&
            0 <= n0 && n0 <= 35 &&
            problem_46_pre_z(n0) &&
            fib4_safe_z(n0) &&
            f != 0 &&
            4 <= i && i <= n0 &&
            a == fib4_z(i - 1) &&
            b == fib4_z(i - 2) &&
            c == fib4_z(i - 3) &&
            d == fib4_z(i - 4) &&
            fib4_z(i) == a + b + c + d &&
            IntArray::seg(f, 0, i + 1, fib4_prefix_z(i + 1)) *
            IntArray::undef_seg(f, i + 1, 100)
        */
    }
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, fib4_fill_len_z(n0, n0 + 1), fib4_prefix_z(fib4_fill_len_z(n0, n0 + 1))) *
        IntArray::undef_seg(f, fib4_fill_len_z(n0, n0 + 1), 100)
    */
    int filled = n + 1;
    if (n < 4) {
        filled = 4;
    }
    /*@ Assert
        n == n0 &&
        filled == fib4_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        filled <= 100 &&
        IntArray::seg(f, 0, filled, fib4_prefix_z(filled)) *
        IntArray::undef_seg(f, filled, 100)
    */
    int result = f[n];
    /*@ Assert
        n == n0 &&
        result == fib4_z(n0) &&
        filled == fib4_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 35 &&
        problem_46_pre_z(n0) &&
        fib4_safe_z(n0) &&
        f != 0 &&
        filled <= 100 &&
        IntArray::seg(f, 0, filled, fib4_prefix_z(filled)) *
        IntArray::undef_seg(f, filled, 100)
    */
    free_int_array(f, filled, 100);
    return result;
}
