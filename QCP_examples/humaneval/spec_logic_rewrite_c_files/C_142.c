/*
"
This function will take a vector of integers. For all entries in the vector, the function shall square the integer entry if its index is a 
multiple of 3 && will cube the integer entry if its index is a multiple of 4 && ! a multiple of 3. The function will ! 
change the entries in the vector whose indexes are ! a multiple of 3 || 4. The function shall then return the sum of all entries. 

Examples:
For lst = {1,2,3} the output should be 6
For lst = {}  the output should be 0
For lst = {-1,-5,2,-1,-5}  the output should be -126
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_142_pre_z: list Z -> Prop)
               (problem_142_spec_z: list Z -> Z -> Prop)
               (sum_prefix_142: Z -> list Z -> Z)
               (sum_squares_int_range_142: list Z -> Prop) */
/*@ Import Coq Require Import coins_142 */

int sum_squares(int* lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_142_pre_z(input_l) &&
        sum_squares_int_range_142(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        problem_142_spec_z(input_l, __return) &&
        IntArray::full(lst, lst_size, input_l)
*/
{
    int sum=0;
    int i;
    /*@ Inv Assert
        lst == lst@pre &&
        lst_size == lst_size@pre &&
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(input_l) &&
        problem_142_pre_z(input_l) &&
        sum_squares_int_range_142(input_l) &&
        0 <= i && i <= lst_size &&
        sum == sum_prefix_142(i, input_l) &&
        INT_MIN <= sum && sum <= INT_MAX &&
        IntArray::full(lst, lst_size, input_l)
    */
    for (i=0;i<lst_size;i++) {
        if (i%3==0) {
            sum+=lst[i]*lst[i];
        } else if (i%4==0) {
            sum+=lst[i]*lst[i]*lst[i];
        } else {
            sum+=lst[i];
        }
        /*@ Assert
            lst == lst@pre &&
            lst_size == lst_size@pre &&
            0 <= lst_size && lst_size < INT_MAX &&
            lst_size == Zlength(input_l) &&
            problem_142_pre_z(input_l) &&
            sum_squares_int_range_142(input_l) &&
            0 <= i && i < lst_size &&
            sum == sum_prefix_142(i + 1, input_l) &&
            INT_MIN <= sum && sum <= INT_MAX &&
            IntArray::full(lst, lst_size, input_l)
        */
    }
    return sum;
}
