/*
Given a non-empty vector of integers lst. add the even elements that are at odd indices..


Examples:
    add({4, 2, 6, 7}) ==> 2 
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_85_pre_z: list Z -> Prop)
               (problem_85_spec_z: list Z -> Z -> Prop)
               (add_prefix_sum_85: Z -> list Z -> Z)
               (add_sum_int_range_85: list Z -> Prop) */
/*@ Import Coq Require Import coins_85 */

int add(int* lst, int lst_size)
/*@ With input_l
    Require
        1 <= lst_size && lst_size <= INT_MAX / 2 &&
        lst_size == Zlength(input_l) &&
        problem_85_pre_z(input_l) &&
        add_sum_int_range_85(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_85_spec_z(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int sum=0;
    int i;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        1 <= lst_size && lst_size <= INT_MAX / 2 &&
        lst_size == Zlength(input_l) &&
        problem_85_pre_z(input_l) &&
        add_sum_int_range_85(input_l) &&
        0 <= i &&
        2 * i <= lst_size &&
        sum == add_prefix_sum_85(i, input_l) &&
        INT_MIN <= sum && sum <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i=0;i*2+1<lst_size;i++) {
        if (lst[i*2+1]%2==0) {
            sum+=lst[i*2+1];
        }
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            1 <= lst_size && lst_size <= INT_MAX / 2 &&
            lst_size == Zlength(input_l) &&
            problem_85_pre_z(input_l) &&
            add_sum_int_range_85(input_l) &&
            0 <= i &&
            2 * i + 1 < lst_size &&
            sum == add_prefix_sum_85(i + 1, input_l) &&
            INT_MIN <= sum && sum <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }
    return sum;
}
