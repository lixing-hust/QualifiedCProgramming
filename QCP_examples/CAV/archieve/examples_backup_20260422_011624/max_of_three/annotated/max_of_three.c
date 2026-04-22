#include "../../verification_stdlib.h"

int max_of_three(int a, int b, int c)
/*@ Require
      INT_MIN <= a && a <= INT_MAX &&
      INT_MIN <= b && b <= INT_MAX &&
      INT_MIN <= c && c <= INT_MAX && emp
    Ensure
      (__return == a@pre || __return == b@pre || __return == c@pre) &&
      __return >= a@pre &&
      __return >= b@pre &&
      __return >= c@pre && emp
*/
{
    int m = a;

    if (b > m) {
        m = b;
    }
    if (c > m) {
        m = c;
    }

    return m;
}
