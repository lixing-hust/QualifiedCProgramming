/*
Given a non-empty vector of integers, return the sum of all of the odd elements that are in even positions.


Examples
solution({5, 8, 7, 1}) ==> 12
solution({3, 3, 3, 3, 3}) ==> 9
solution({30, 13, 24, 321}) ==>0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_121_pre_z: list Z -> Prop)
               (problem_121_spec_z: list Z -> Z -> Prop)
               (sum_prefix_121: Z -> list Z -> Z)
               (sum_121_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_121 */

int solutions(int* lst, int lst_size)
/*@ With input_l
    Require
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_121_pre_z(input_l) &&
        sum_121_int_range(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_121_spec_z(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int sum=0;
    int i;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_121_pre_z(input_l) &&
        sum_121_int_range(input_l) &&
        0 <= i &&
        2 * i <= lst_size + 1 &&
        sum == sum_prefix_121(i, input_l) &&
        0 <= sum && sum <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i=0;i*2<lst_size;i++) {
        if (lst[i*2]%2==1) {
            sum+=lst[i*2];
        }
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            1 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_121_pre_z(input_l) &&
            sum_121_int_range(input_l) &&
            0 <= i &&
            2 * i < lst_size &&
            sum == sum_prefix_121(i + 1, input_l) &&
            0 <= sum && sum <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }
    /*@ Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_121_pre_z(input_l) &&
        sum_121_int_range(input_l) &&
        0 <= i &&
        2 * i >= lst_size &&
        2 * i <= lst_size + 1 &&
        sum == sum_prefix_121(i, input_l) &&
        0 <= sum && sum <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    return sum;
}
