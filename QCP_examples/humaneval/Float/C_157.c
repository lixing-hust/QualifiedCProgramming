/*
Given the lengths of the three sides of a triangle. Return true if the three
sides form a right-angled triangle, false otherwise.
*/
#include "verification_stdlib.h"

/*@ Extern Coq
      (problem_157_pre : fp32 -> fp32 -> fp32 -> Prop)
      (problem_157_spec : fp32 -> fp32 -> fp32 -> Z -> Prop)
*/
/*@ Import Coq Require Import coins_157 */

int right_angle_triangle(float a, float b, float c)
/*@ Require problem_157_pre(a, b, c) && emp
    Ensure problem_157_spec(a, b, c, __return) && emp
*/
{
    float aa = a * a;
    float bb = b * b;
    float cc = c * c;
    float d1 = (aa + bb) - cc;
    float d2 = (aa + cc) - bb;
    float d3 = (bb + cc) - aa;
    float lower = -0.0001f;
    float upper = 0.0001f;

    if (lower < d1) {
        if (d1 < upper) return 1;
    }
    if (lower < d2) {
        if (d2 < upper) return 1;
    }
    if (lower < d3) {
        if (d3 < upper) return 1;
    }
    return 0;
}
