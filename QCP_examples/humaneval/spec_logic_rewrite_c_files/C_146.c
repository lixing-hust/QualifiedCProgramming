/*
Write a function that takes a vector of numbers as input && returns
the number of elements in the vector that are greater than 10 && both
first && last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter({15, -73, 14, -15}) => 1
specialFilter({33, -2, -3, 45, 21, 109}) => 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_146_pre_z: list Z -> Prop)
               (problem_146_spec_z: list Z -> Z -> Prop)
               (special_filter_safe_146: list Z -> Prop)
               (special_filter_prefix_146: list Z -> Z -> Z -> Prop)
               (first_digit_state_146: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_146 */

int specialFilter(int* nums, int nums_size)
/*@ With input_l
    Require
        nums != 0 &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_146_pre_z(input_l) &&
        special_filter_safe_146(input_l) &&
        IntArray::full(nums, nums_size, input_l)
    Ensure
        problem_146_spec_z(input_l, __return) &&
        IntArray::full(nums, nums_size, input_l)
*/
{
    int num = 0;
    int i;
    /*@ Inv Assert
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_146_pre_z(input_l) &&
        special_filter_safe_146(input_l) &&
        0 <= i && i <= nums_size &&
        0 <= num && num <= i &&
        special_filter_prefix_146(input_l, i, num) &&
        IntArray::full(nums, nums_size, input_l)
    */
    for (i = 0; i < nums_size; i++) {
        int current = nums[i];
        /*@ Assert
            nums == nums@pre &&
            nums_size == nums_size@pre &&
            0 <= nums_size && nums_size < INT_MAX &&
            nums_size == Zlength(input_l) &&
            problem_146_pre_z(input_l) &&
            special_filter_safe_146(input_l) &&
            0 <= i && i < nums_size &&
            0 <= num && num <= i &&
            current == Znth(i, input_l, 0) &&
            INT_MIN <= current && current <= INT_MAX &&
            special_filter_prefix_146(input_l, i, num) &&
            IntArray::full(nums, nums_size, input_l)
        */
        if (current > 10) {
            int first = current;
            int last = current % 10;
            /*@ Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_safe_146(input_l) &&
                0 <= i && i < nums_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                current > 10 &&
                INT_MIN <= current && current <= INT_MAX &&
                first == current &&
                last == current % 10 &&
                first_digit_state_146(current, first) &&
                special_filter_prefix_146(input_l, i, num) &&
                IntArray::full(nums, nums_size, input_l)
            */
            /*@ Inv Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_safe_146(input_l) &&
                0 <= i && i < nums_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                current > 10 &&
                INT_MIN <= current && current <= INT_MAX &&
                1 <= first && first <= current &&
                last == current % 10 &&
                first_digit_state_146(current, first) &&
                special_filter_prefix_146(input_l, i, num) &&
                IntArray::full(nums, nums_size, input_l)
            */
            while (first >= 10) {
                first /= 10;
            }
            /*@ Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_safe_146(input_l) &&
                0 <= i && i < nums_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                current > 10 &&
                INT_MIN <= current && current <= INT_MAX &&
                1 <= first && first < 10 &&
                last == current % 10 &&
                first_digit_state_146(current, first) &&
                special_filter_prefix_146(input_l, i, num) &&
                IntArray::full(nums, nums_size, input_l)
            */
            if (first % 2 == 1 && last % 2 == 1) {
                num += 1;
                /*@ Assert
                    nums == nums@pre &&
                    nums_size == nums_size@pre &&
                    0 <= nums_size && nums_size < INT_MAX &&
                    nums_size == Zlength(input_l) &&
                    problem_146_pre_z(input_l) &&
                    special_filter_safe_146(input_l) &&
                    0 <= i && i < nums_size &&
                    0 <= num && num <= i + 1 &&
                    current == Znth(i, input_l, 0) &&
                    current > 10 &&
                    first_digit_state_146(current, first) &&
                    first < 10 &&
                    last == current % 10 &&
                    first % 2 == 1 &&
                    last % 2 == 1 &&
                    special_filter_prefix_146(input_l, i + 1, num) &&
                    IntArray::full(nums, nums_size, input_l)
                */
            } else {
                /*@ Assert
                    nums == nums@pre &&
                    nums_size == nums_size@pre &&
                    0 <= nums_size && nums_size < INT_MAX &&
                    nums_size == Zlength(input_l) &&
                    problem_146_pre_z(input_l) &&
                    special_filter_safe_146(input_l) &&
                    0 <= i && i < nums_size &&
                    0 <= num && num <= i &&
                    current == Znth(i, input_l, 0) &&
                    current > 10 &&
                    first_digit_state_146(current, first) &&
                    first < 10 &&
                    last == current % 10 &&
                    (first % 2 != 1 || last % 2 != 1) &&
                    special_filter_prefix_146(input_l, i + 1, num) &&
                    IntArray::full(nums, nums_size, input_l)
                */
            }
        } else {
            /*@ Assert
                nums == nums@pre &&
                nums_size == nums_size@pre &&
                0 <= nums_size && nums_size < INT_MAX &&
                nums_size == Zlength(input_l) &&
                problem_146_pre_z(input_l) &&
                special_filter_safe_146(input_l) &&
                0 <= i && i < nums_size &&
                0 <= num && num <= i &&
                current == Znth(i, input_l, 0) &&
                current <= 10 &&
                special_filter_prefix_146(input_l, i + 1, num) &&
                IntArray::full(nums, nums_size, input_l)
            */
        }
    }
    return num;
}
