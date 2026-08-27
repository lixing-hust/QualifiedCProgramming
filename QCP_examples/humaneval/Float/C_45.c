/*
Given length of a side && high return area for a triangle.
>>> triangle_area(5, 3)
7.5
*/
#include "verification_stdlib.h"

/*@ Extern Coq
      (problem_45_pre : fp32 -> fp32 -> Prop)
      (triangle_area_fp32 : fp32 -> fp32 -> fp32)
*/
/*@ Import Coq Require Import coins_45 */

float triangle_area(float a, float h)
/*@ Require problem_45_pre(a, h) && emp
    Ensure __return == triangle_area_fp32(a, h) && emp
*/
{
    float area = (a * h) * 0.5f;
    return area;

}
