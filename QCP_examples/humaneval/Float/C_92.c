/*
Create a function that takes three numbers. Return true if one number equals
the sum of the other two and all three numbers are integers.
*/
#include "verification_stdlib.h"

/*@ Extern Coq
      (fp32_of_bits : Z -> fp32)
      (problem_92_pre : fp32 -> fp32 -> fp32 -> Prop)
      (problem_92_spec : fp32 -> fp32 -> fp32 -> Z -> Prop)
      (roundf_fixed_bits_92 : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import coins_92 */

float roundf(float number)
/*@ With (input_bits : Z)
    Require number == fp32_of_bits(input_bits) &&
            fp32_isFinite(number) && emp
    Ensure exists result_bits,
           __return == fp32_of_bits(result_bits) &&
           fp32_isFinite(__return) &&
           roundf_fixed_bits_92(input_bits, result_bits) && emp
*/;

int any_int(float a, float b, float c)
/*@ With (a_bits : Z) (b_bits : Z) (c_bits : Z)
    Require a == fp32_of_bits(a_bits) &&
            b == fp32_of_bits(b_bits) &&
            c == fp32_of_bits(c_bits) &&
            fp32_isFinite(a) &&
            fp32_isFinite(b) &&
            fp32_isFinite(c) &&
            problem_92_pre(a, b, c) && emp
    Ensure problem_92_spec(a, b, c, __return) && emp
*/
{
    float rounded_a = roundf(a) /*@ where input_bits = a_bits */;
    if (rounded_a != a) return 0;

    float rounded_b = roundf(b) /*@ where input_bits = b_bits */;
    if (rounded_b != b) return 0;

    float rounded_c = roundf(c) /*@ where input_bits = c_bits */;
    if (rounded_c != c) return 0;

    float sum_ab = a + b;
    if (sum_ab == c) return 1;

    float sum_ac = a + c;
    if (sum_ac == b) return 1;

    float sum_bc = b + c;
    if (sum_bc == a) return 1;

    return 0;
}
