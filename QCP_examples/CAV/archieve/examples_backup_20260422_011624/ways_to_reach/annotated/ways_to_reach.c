#include "../../verification_stdlib.h"

/*@ Extern Coq (ways_to_reach_z: Z -> Z) */
/*@ Import Coq Require Import ways_to_reach */

int ways_to_reach(int n)
/*@ Require
      0 <= n && n <= 45 && emp
    Ensure
      __return == ways_to_reach_z(n@pre) && emp
*/
{
    int i;
    int a = 1;
    int b = 1;
    int c;

    if (n == 0) {
        return 1;
    }

    /*@ Inv
          2 <= i && i <= n + 1 &&
          n == n@pre &&
          a == ways_to_reach_z(i - 2) &&
          b == ways_to_reach_z(i - 1) &&
          emp
    */
    for (i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }

    return b;
}
