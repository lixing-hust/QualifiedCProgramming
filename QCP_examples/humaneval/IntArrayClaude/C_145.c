/*
Write a function which sorts the given vector of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original vector.

For example:
>>> order_by_points({1, 11, -1, -11, -12}) == {-1, -11, 1, -12, 11}
>>> order_by_points({}) == {}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_145_pre_z: list Z -> Prop)
               (problem_145_spec_z: list Z -> list Z -> Prop)
               (signed_digit_score_result: Z -> Z -> Prop)
               (signed_digit_tail_state: Z -> Z -> Z -> Prop)
               (first_digit_state_145: Z -> Z -> Prop)
               (highest_power10_state: Z -> Z -> Z -> Z -> Prop)
               (order_copy_prefix: Z -> list Z -> list Z -> list Z -> Prop)
               (order_sort_outer_state: Z -> list Z -> list Z -> list Z -> Prop)
               (order_sort_inner_state: Z -> Z -> list Z -> list Z -> list Z -> Prop)
               (order_by_points_int_range: list Z -> Prop) */
/*@ Import Coq Require Import coins_145 */

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

void free_int_array(int *array, int size)
/*@ With l
    Require
        array != 0 &&
        0 <= size && size < INT_MAX &&
        size == Zlength(l) &&
        IntArray::full(array, size, l)
    Ensure emp
*/;

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

int signed_digit_score(int x)
    /*@ Require
        INT_MIN < x && x < INT_MAX && x <= INT_MAX &&
        Zabs(x) < 100000000 &&
        emp
    Ensure
        signed_digit_score_result(x, __return) &&
        emp
*/
{
    int t = abs(x);
    int msd = 0;
    int sum = 0;
    /*@ Inv Assert
        INT_MIN < x && x < INT_MAX &&
        x == x@pre &&
        Zabs(x) < 100000000 &&
        0 <= t && t < 100000000 &&
        sum == 0 &&
        first_digit_state_145(Zabs(x@pre), t) &&
        data_at(&msd, msd)
    */
    while (t >= 10) t /= 10;
    msd = t;
    sum += (x >= 0) ? msd : -msd;
    t = abs(x);
    if (t >= 10) {
        int p = 1;
        /*@ Inv Assert
            INT_MIN < x && x < INT_MAX &&
            x == x@pre &&
            Zabs(x) < 100000000 &&
            10 <= t && t < 100000000 &&
            1 <= p && p <= t &&
            INT_MIN + 10 <= sum && sum <= INT_MAX - 10 &&
            highest_power10_state(x@pre, t, p, sum) &&
            data_at(&msd, msd)
        */
        while (p * 10 <= t) p *= 10;
        t %= p;
    } else t = 0;
    /*@ Inv Assert
        INT_MIN < x && x < INT_MAX &&
        x == x@pre &&
        Zabs(x) < 100000000 &&
        0 <= t && t < 100000000 &&
        -100 <= sum && sum <= 100 &&
        signed_digit_tail_state(x@pre, t, sum) &&
        data_at(&msd, msd)
    */
    while (t > 0) {
        sum += t % 10;
        t /= 10;
    }
    return sum;
}

IntArray *order_by_points(int* nums, int nums_size)
/*@ With input_l
    Require
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_145_pre_z(input_l) &&
        order_by_points_int_range(input_l) &&
        IntArray::full(nums, nums_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == nums_size &&
        output_size == Zlength(output_l) &&
        problem_145_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(nums, nums_size, input_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    int* score;
    out->size = nums_size;
    out->data = malloc_int_array(nums_size);
    score = malloc_int_array(nums_size);
    int *data = out->data;
    if (data == 0 || score == 0) {
        out->size = 0;
        return out;
    }
    int i;
    /*@ Inv Assert
        exists output_l score_l,
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        out != 0 &&
        data != 0 &&
        score != 0 &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_145_pre_z(input_l) &&
        order_by_points_int_range(input_l) &&
        0 <= i && i <= nums_size &&
        i == Zlength(output_l) &&
        i == Zlength(score_l) &&
        order_copy_prefix(i, input_l, output_l, score_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), nums_size) *
        IntArray::full(nums, nums_size, input_l) *
        IntArray::seg(data, 0, i, output_l) *
        IntArray::undef_seg(data, i, nums_size) *
        IntArray::seg(score, 0, i, score_l) *
        IntArray::undef_seg(score, i, nums_size)
    */
    for (i=0;i<nums_size;i++) {
        data[i] = nums[i];
        score[i] = signed_digit_score(nums[i]);
        /*@ Assert
            exists output_l score_l,
            nums == nums@pre &&
            nums_size == nums_size@pre &&
            out != 0 &&
            data != 0 &&
            score != 0 &&
            0 <= nums_size && nums_size < INT_MAX &&
            nums_size == Zlength(input_l) &&
            problem_145_pre_z(input_l) &&
            order_by_points_int_range(input_l) &&
            0 <= i && i < nums_size &&
            i + 1 == Zlength(output_l) &&
            i + 1 == Zlength(score_l) &&
            order_copy_prefix(i + 1, input_l, output_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), nums_size) *
            IntArray::full(nums, nums_size, input_l) *
            IntArray::seg(data, 0, i + 1, output_l) *
            IntArray::undef_seg(data, i + 1, nums_size) *
            IntArray::seg(score, 0, i + 1, score_l) *
            IntArray::undef_seg(score, i + 1, nums_size)
        */
    }
    /*@ Inv Assert
        exists output_l score_l,
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        out != 0 &&
        data != 0 &&
        score != 0 &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_145_pre_z(input_l) &&
        order_by_points_int_range(input_l) &&
        0 <= i && i <= nums_size &&
        nums_size == Zlength(output_l) &&
        nums_size == Zlength(score_l) &&
        order_sort_outer_state(i, input_l, output_l, score_l) &&
        data_at(&(out -> data), data) *
        data_at(&(out -> size), nums_size) *
        IntArray::full(nums, nums_size, input_l) *
        IntArray::full(data, nums_size, output_l) *
        IntArray::full(score, nums_size, score_l)
    */
    for (i=0;i<nums_size;i++) {
        int j;
        /*@ Inv Assert
            exists output_l score_l,
            nums == nums@pre &&
            nums_size == nums_size@pre &&
            out != 0 &&
            data != 0 &&
            score != 0 &&
            0 <= nums_size && nums_size < INT_MAX &&
            nums_size == Zlength(input_l) &&
            problem_145_pre_z(input_l) &&
            order_by_points_int_range(input_l) &&
            0 <= i && i < nums_size &&
            1 <= j && j <= nums_size &&
            nums_size == Zlength(output_l) &&
            nums_size == Zlength(score_l) &&
            order_sort_inner_state(i, j, input_l, output_l, score_l) &&
            data_at(&(out -> data), data) *
            data_at(&(out -> size), nums_size) *
            IntArray::full(nums, nums_size, input_l) *
            IntArray::full(data, nums_size, output_l) *
            IntArray::full(score, nums_size, score_l)
        */
        for (j=1;j<nums_size;j++)
        if (score[j-1]>score[j])
        {
            int m=score[j];score[j]=score[j-1];score[j-1]=m;
            m=data[j];data[j]=data[j-1];data[j-1]=m;
        }
        /*@ Assert
            exists output_l score_l,
            nums == nums@pre &&
            nums_size == nums_size@pre &&
            out != 0 &&
            data != 0 &&
            score != 0 &&
            0 <= nums_size && nums_size < INT_MAX &&
            nums_size == Zlength(input_l) &&
            problem_145_pre_z(input_l) &&
            order_by_points_int_range(input_l) &&
            0 <= i && i < nums_size &&
            nums_size == Zlength(output_l) &&
            nums_size == Zlength(score_l) &&
            order_sort_outer_state(i + 1, input_l, output_l, score_l) &&
            data_at(&j, nums_size) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), nums_size) *
            IntArray::full(nums, nums_size, input_l) *
            IntArray::full(data, nums_size, output_l) *
            IntArray::full(score, nums_size, score_l)
        */
    }
    /*@ Assert
        exists output_l score_l,
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        out != 0 &&
        data != 0 &&
        score != 0 &&
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        nums_size == Zlength(output_l) &&
            nums_size == Zlength(score_l) &&
            problem_145_spec_z(input_l, output_l) &&
            data_at(&i, nums_size) *
            data_at(&(out -> data), data) *
            data_at(&(out -> size), nums_size) *
            IntArray::full(nums, nums_size, input_l) *
        IntArray::full(data, nums_size, output_l) *
        IntArray::full(score, nums_size, score_l)
    */
    free_int_array(score, nums_size);
    return out;
}
