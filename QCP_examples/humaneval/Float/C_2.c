/*
Given a positive floating point number, it can be decomposed into
&& integer part (largest integer smaller than given number) && decimals
(leftover part always smaller than 1).

Return the decimal part of the number.
>>> truncate_number(3.5)
0.5
*/
#include "verification_stdlib.h"

/*@ Extern Coq
      (fp32_of_bits : Z -> fp32)
      (problem_2_pre_bits : Z -> Prop)
      (problem_2_spec_bits : Z -> Z -> Prop)
      (floorf_rel_bits_2 : Z -> Z -> Prop)
      (floorf_fraction_bits_2 : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import coins_2 */

float floorf(float number)
/*@ With (input_bits : Z)
    Require number == fp32_of_bits(input_bits) &&
            problem_2_pre_bits(input_bits) && emp
    Ensure exists floor_bits fraction_bits,
           __return == fp32_of_bits(floor_bits) &&
           floorf_rel_bits_2(input_bits, floor_bits) &&
           fp32_sub(number, __return) == fp32_of_bits(fraction_bits) &&
           fp32_isFinite(fp32_sub(number, __return)) &&
           floorf_fraction_bits_2(input_bits, fraction_bits) && emp
*/;

float truncate_number(float number)
/*@ With (input_bits : Z)
    Require number == fp32_of_bits(input_bits) &&
            problem_2_pre_bits(input_bits) && emp
    Ensure exists result_bits,
           __return == fp32_of_bits(result_bits) &&
           problem_2_spec_bits(input_bits, result_bits) && emp
*/
{
    float integer_part = floorf(number)
      /*@ where input_bits = input_bits */;
    return number - integer_part;
}
