/*
Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter([15, -73, 14, -15]) => 1
specialFilter([33, -2, -3, 45, 21, 109]) => 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_146_pre_z: list Z -> Prop)
               (problem_146_spec_z: list Z -> Z -> Prop)
               (special_filter_prefix: Z -> list Z -> Z -> Prop)
               (special_filter_int_range: list Z -> Prop)
               (first_digit_state: Z -> Z -> Prop)
               (special_number_c: Z -> Prop)
               (not_special_number_c: Z -> Prop) */
/*@ Import Coq Require Import coins_146 */

int specialFilter(int* nums, int nums_size)
/*@ With input_l
    Require
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_146_pre_z(input_l) &&
        special_filter_int_range(input_l) &&
        IntArray::full(nums, nums_size, input_l)
    Ensure
        problem_146_spec_z(input_l, __return) &&
        IntArray::full(nums, nums_size, input_l)
*/
{
    int num=0;
    int i;
    /*@ Inv Assert
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_146_pre_z(input_l) &&
        special_filter_int_range(input_l) &&
        0 <= i && i <= nums_size &&
        special_filter_prefix(i, input_l, num) &&
        IntArray::full(nums, nums_size, input_l)
    */
    for (i=0;i<nums_size;i++) {
        if (nums[i]>10)
        {
            int first;
            int last;
            first = nums[i];
            last = nums[i] % 10;
            /*@ Inv Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_int_range(input_l) &&
                0 <= i && i < nums_size &&
                special_filter_prefix(i, input_l, num) &&
                10 < Znth(i, input_l, 0) &&
                0 <= last && last <= 9 &&
                last == Znth(i, input_l, 0) % 10 &&
                first_digit_state(Znth(i, input_l, 0), first) &&
                IntArray::full(nums, nums_size, input_l)
            */
            while (first >= 10) {
                first /= 10;
            }
            if (first % 2 == 1 && last % 2 == 1) {
                /*@ Assert
                    nums == nums@pre &&
                    nums_size == nums_size@pre &&
                    0 <= nums_size && nums_size < INT_MAX &&
                    nums_size == Zlength(input_l) &&
                    problem_146_pre_z(input_l) &&
                    special_filter_int_range(input_l) &&
                    0 <= i && i < nums_size &&
                    special_filter_prefix(i, input_l, num) &&
                    special_number_c(Znth(i, input_l, 0)) &&
                    data_at(&first, first) *
                    data_at(&last, last) *
                    IntArray::full(nums, nums_size, input_l)
                */
                num+=1;
            }
            /*@ Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_int_range(input_l) &&
                0 <= i && i < nums_size &&
                special_filter_prefix(i + 1, input_l, num) &&
                data_at(&first, first) *
                data_at(&last, last) *
                IntArray::full(nums, nums_size, input_l)
            */
        }
        /*@ Assert
            nums == nums@pre &&
            nums_size == nums_size@pre &&
            0 <= nums_size && nums_size < INT_MAX &&
            nums_size == Zlength(input_l) &&
            problem_146_pre_z(input_l) &&
            special_filter_int_range(input_l) &&
            0 <= i && i < nums_size &&
            special_filter_prefix(i + 1, input_l, num) &&
            IntArray::full(nums, nums_size, input_l)
        */
    }
    return num;
}
