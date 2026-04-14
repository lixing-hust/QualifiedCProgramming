/*
From a given vector of deposit && withdrawal operations on a bank account that starts with
zero balance, detect if at any point the balance falls below zero.
>>> below_zero({1, 2, 3})
0
>>> below_zero({1, 2, -4, 5})
1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_3_pre: list Z -> Prop) */
/*@ Extern Coq (problem_3_spec: list Z -> bool -> Prop) */
/*@ Extern Coq (list_int_range: list Z -> Z -> Prop) */
/*@ Extern Coq (prefix_sums_int_range: list Z -> Z -> Prop) */
/*@ Extern Coq (true: bool) (false: bool) */
/*@ Import Coq Require Import coins_3 */

int below_zero(int *operations, int operations_size)
/*@ With l
    Require
        0 <= operations_size && operations_size < INT_MAX &&
        Zlength(l) == operations_size &&
        list_int_range(l, operations_size) &&
        prefix_sums_int_range(l, operations_size) &&
        problem_3_pre(l) &&
        IntArray::full(operations, operations_size, l)
    Ensure
        ((__return != 0) && problem_3_spec(l, true) ||
         (__return == 0) && problem_3_spec(l, false)) &&
        IntArray::full(operations, operations_size, l)
*/
{
    int num = 0;
    int i;
    /*@ Inv
        num == sum(sublist(0, i, l)) &&
        0 <= i && i <= operations_size@pre &&
        Zlength(l) == operations_size@pre &&
        list_int_range(l, operations_size@pre) &&
        prefix_sums_int_range(l, operations_size@pre) &&
        problem_3_pre(l) &&
        (forall (k: Z), (0 <= k && k < i) => 0 <= sum(sublist(0, k + 1, l))) &&
        IntArray::full(operations@pre, operations_size@pre, l)
    */
    for (i = 0; i < operations_size; i++) {
        num += operations[i];
        if (num < 0) return 1;
    }
    return 0;
}
