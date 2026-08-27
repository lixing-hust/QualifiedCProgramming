/*
Check if in given vector of numbers, are any two numbers closer to each other than
given threshold.
>>> has_close_elements({1.0, 2.0, 3.0}, 0.5)
false
>>> has_close_elements({1.0, 2.8, 3.0, 4.0, 5.0, 2.0}, 0.3)
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq
      (FloatArray::full : Z -> Z -> list fp32 -> Assertion)
      (FloatArray::missing_i : Z -> Z -> Z -> Z -> list fp32 -> Assertion)
      (problem_0_pre_z : fp32 -> Prop)
      (problem_0_spec_z : list fp32 -> fp32 -> Z -> Prop)
      (no_close_before_i_0 : list fp32 -> fp32 -> Z -> Prop)
      (no_close_before_j_0 : list fp32 -> fp32 -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import coins_0 */

int has_close_elements(float *numbers, int numbers_size, float threshold)
/*@ With numbers_l
    Require
      0 <= numbers_size && numbers_size < INT_MAX &&
      problem_0_pre_z(threshold) &&
      FloatArray::full(numbers, numbers_size, numbers_l)
    Ensure
      problem_0_spec_z(numbers_l, threshold, __return) &&
      FloatArray::full(numbers, numbers_size, numbers_l)
*/
{
    int i, j;

    i = 0;
    /*@ Inv Assert
          numbers == numbers@pre &&
          numbers_size == numbers_size@pre &&
          threshold == threshold@pre &&
          0 <= i && i <= numbers_size &&
          no_close_before_i_0(numbers_l, threshold, i) &&
          undef_data_at(&j) *
          FloatArray::full(numbers, numbers_size, numbers_l)
    */
    for (; i < numbers_size; i++)
    {
        j = i + 1;
        /*@ Inv Assert
              numbers == numbers@pre &&
              numbers_size == numbers_size@pre &&
              threshold == threshold@pre &&
              0 <= i && i < numbers_size &&
              i + 1 <= j && j <= numbers_size &&
              no_close_before_i_0(numbers_l, threshold, i) &&
              no_close_before_j_0(numbers_l, threshold, i, j) &&
              FloatArray::full(numbers, numbers_size, numbers_l)
        */
        for (; j < numbers_size; j++)
        {
            float difference = numbers[i] - numbers[j];
            if (difference < 0.0f) {
                difference = -difference;
            }
            if (difference < threshold) {
                return 1;
            }
        }
    }

    return 0;
}
