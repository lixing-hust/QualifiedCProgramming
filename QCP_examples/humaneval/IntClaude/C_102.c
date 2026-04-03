/*
This function takes two positive numbers x && y && returns the
biggest even integer number that is in the range [x, y] inclusive. If
there's no such number, then the function should return -1.

For example:
choose_num(12, 15) = 14
choose_num(13, 12) = -1
*/
#include "../../verification_stdlib.h"
/*@ Extern Coq (problem_102_pre: Z -> Z -> Prop) */
/*@ Extern Coq (problem_102_spec: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_102 */
int choose_num(int x, int y)
/*@ Require
        problem_102_pre(x, y) &&
        1 <= x && x <= INT_MAX &&
        1 <= y && y <= INT_MAX && emp
    Ensure
        problem_102_spec(x@pre, y@pre, __return) && emp
*/
{
    if (y<x) return -1;
    if (y==x && y%2==1) return -1;
    if (y%2==1) return y-1;
    return y;
}
