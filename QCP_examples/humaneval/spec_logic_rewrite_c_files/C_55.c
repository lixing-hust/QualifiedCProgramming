/*
Return n-th Fibonacci number.
>>> fib(10)
55
>>> fib(1)
1
>>> fib(8)
21
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_55_pre_z: Z -> Prop)
               (problem_55_spec_z: Z -> Z -> Prop)
               (fib_z: Z -> Z)
               (fib_prefix_z: Z -> list Z)
               (fib_fill_len_z: Z -> Z -> Z)
               (fib_safe_z: Z -> Prop) */
/*@ Import Coq Require Import coins_55 */

int *malloc_int_array(int size)
/*@ Require
        size == 1000 && emp
    Ensure
        __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int init_size, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= init_size && init_size <= size &&
        size == 1000 &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        emp
*/;

int fib(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) && emp
    Ensure
        problem_55_spec_z(n0, __return) && emp
*/
{
    int *f = malloc_int_array(1000);
    f[0]=0;f[1]=1;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, 2, fib_prefix_z(2)) *
        IntArray::undef_seg(f, 2, 1000)
    */
    /*@ Inv Assert
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        2 <= i && i <= 47 &&
        (n0 < 2 && i == 2 || 2 <= n0 && i <= n0 + 1) &&
        IntArray::seg(f, 0, fib_fill_len_z(n0, i), fib_prefix_z(fib_fill_len_z(n0, i))) *
        IntArray::undef_seg(f, fib_fill_len_z(n0, i), 1000)
    */
    for (int i=2;i<=n; i++)
    {
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        2 <= i && i <= n0 &&
        fib_fill_len_z(n0, i) == i &&
        IntArray::seg(f, 0, i, fib_prefix_z(i)) *
        IntArray::undef_seg(f, i, 1000)
    */
    int a = f[i-1];
    int b = f[i-2];
    f[i]=a+b;
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        2 <= i && i <= n0 &&
        a == fib_z(i - 1) &&
        b == fib_z(i - 2) &&
        fib_z(i) == a + b &&
        IntArray::seg(f, 0, i + 1, fib_prefix_z(i + 1)) *
        IntArray::undef_seg(f, i + 1, 1000)
    */
    }
    /*@ Assert
        n == n0 &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        IntArray::seg(f, 0, fib_fill_len_z(n0, n0 + 1), fib_prefix_z(fib_fill_len_z(n0, n0 + 1))) *
        IntArray::undef_seg(f, fib_fill_len_z(n0, n0 + 1), 1000)
    */
    int filled = n + 1;
    if (n < 2) {
        filled = 2;
    }
    /*@ Assert
        n == n0 &&
        filled == fib_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        filled <= 1000 &&
        IntArray::seg(f, 0, filled, fib_prefix_z(filled)) *
        IntArray::undef_seg(f, filled, 1000)
    */
    int result = f[n];
    /*@ Assert
        n == n0 &&
        result == fib_z(n0) &&
        filled == fib_fill_len_z(n0, n0 + 1) &&
        n0 < filled &&
        0 <= n0 && n0 <= 46 &&
        problem_55_pre_z(n0) &&
        fib_safe_z(n0) &&
        f != 0 &&
        filled <= 1000 &&
        IntArray::seg(f, 0, filled, fib_prefix_z(filled)) *
        IntArray::undef_seg(f, filled, 1000)
    */
    free_int_array(f, filled, 1000);
    return result;
}
