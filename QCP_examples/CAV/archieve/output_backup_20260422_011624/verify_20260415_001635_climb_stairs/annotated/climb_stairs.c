#include "../../../../verification_stdlib.h"

/*@ Extern Coq (climb_stairs_z: Z -> Z) */
/*@ Import Coq Require Import climb_stairs */

int climbStairs(int n)
/*@ Require
      0 <= n && n <= 45 && emp
    Ensure
      __return == climb_stairs_z(n@pre) && emp
*/
{
    if (n <= 1) {
        return 1;
    }

    int prev2 = 1;
    int prev1 = 1;
    int cur = 1;
    int i;

    /*@ Inv
          n == n@pre &&
          2 <= i && i <= n@pre + 1 &&
          prev2 == climb_stairs_z(i - 2) &&
          prev1 == climb_stairs_z(i - 1) &&
          cur == prev1
    */
    for (i = 2; i <= n; i++) {
        cur = prev1 + prev2;
        prev2 = prev1;
        prev1 = cur;
    }

    return cur;
}
