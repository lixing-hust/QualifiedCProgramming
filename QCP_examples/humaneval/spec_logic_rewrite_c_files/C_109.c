/*
We have a vector "arr" of N integers arr[1], arr[2], ..., arr[N].The
numbers in the vector will be randomly ordered. Your task is to determine if
it is possible to get a vector sorted in non-decreasing order by performing 
the following operation on the given vector:
    You are allowed to perform right shift operation any number of times.

One right shift operation means shifting all elements of the vector by one
position in the right direction. The last element of the vector will be moved to
the starting position in the vector i.e. 0th index. 

If it is possible to obtain the sorted vector by performing the above operation
then return true else return false.
If the given vector is empty then return true.

Note: The given vector is guaranteed to have unique elements.

For Example:

move_one_ball({3, 4, 5, 1, 2})==>true
Explanation: By performing 2 right shift operations, non-decreasing order can
             be achieved for the given vector.
move_one_ball({3, 5, 4, 1, 2})==>false
Explanation:It is ! possible to get non-decreasing order for the given
            vector by performing any number of right shift operations.
            
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_109_pre_z: list Z -> Prop)
               (problem_109_spec_z: list Z -> bool -> Prop)
               (move_one_ball_safe_109: list Z -> Prop)
               (move_one_ball_prefix_109: list Z -> Z -> Z -> Prop)
               (move_one_ball_wrap_109: list Z -> Z -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import coins_109 */

int move_one_ball(int* arr, int arr_size)
/*@ With input_l
    Require
        arr != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_109_pre_z(input_l) &&
        move_one_ball_safe_109(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        ((__return != 0 && problem_109_spec_z(input_l, true)) ||
         (__return == 0 && problem_109_spec_z(input_l, false))) &&
        IntArray::full(arr, arr_size, input_l)
*/
{
    int num=0;
    if (arr_size==0) return 1;
    int i;
    /*@ Inv Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_109_pre_z(input_l) &&
        move_one_ball_safe_109(input_l) &&
        1 <= i && i <= arr_size &&
        0 <= num && num <= i &&
        move_one_ball_prefix_109(input_l, i, num) &&
        IntArray::full(arr, arr_size, input_l)
    */
    for (i=1;i<arr_size;i++)
        if (arr[i]<arr[i-1]) {
            num+=1;
            /*@ Assert
                arr == arr@pre &&
                arr_size == arr_size@pre &&
                0 <= arr_size && arr_size < INT_MAX &&
                arr_size == Zlength(input_l) &&
                problem_109_pre_z(input_l) &&
                move_one_ball_safe_109(input_l) &&
                1 <= i && i < arr_size &&
                0 <= num && num <= i + 1 &&
                move_one_ball_prefix_109(input_l, i + 1, num) &&
                IntArray::full(arr, arr_size, input_l)
            */
        } else {
            /*@ Assert
                arr == arr@pre &&
                arr_size == arr_size@pre &&
                0 <= arr_size && arr_size < INT_MAX &&
                arr_size == Zlength(input_l) &&
                problem_109_pre_z(input_l) &&
                move_one_ball_safe_109(input_l) &&
                1 <= i && i < arr_size &&
                0 <= num && num <= i &&
                move_one_ball_prefix_109(input_l, i + 1, num) &&
                IntArray::full(arr, arr_size, input_l)
            */
        }
    if (arr[arr_size-1]>arr[0]) num+=1;
    /*@ Assert
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        0 < arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_109_pre_z(input_l) &&
        move_one_ball_safe_109(input_l) &&
        0 <= num && num <= arr_size &&
        move_one_ball_wrap_109(input_l, num) &&
        IntArray::full(arr, arr_size, input_l) *
        data_at(&i, i)
    */
    if (num<2) return 1;
    return 0;
}
