#include "../../verification_stdlib.h"

int max_of_two(int a, int b)
/*@ Require
      INT_MIN <= a && a <= INT_MAX &&
      INT_MIN <= b && b <= INT_MAX && emp
    Ensure
      (__return == a@pre || __return == b@pre) &&
      __return >= a@pre &&
      __return >= b@pre && emp
*/
{
    if (a >= b) {
        return a;
    } else {
        return b;
    }
}
