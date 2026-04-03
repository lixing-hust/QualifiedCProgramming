#include "../verification_stdlib.h"

int car_race_collision(int n)
/*@ Require
        INT_MIN <= n && n <= INT_MAX && emp
    Ensure
        __return == n * n && emp
*/
{
    return n*n;
}