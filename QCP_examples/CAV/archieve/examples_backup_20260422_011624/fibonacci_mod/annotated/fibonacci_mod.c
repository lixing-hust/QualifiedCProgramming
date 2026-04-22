#include "../../verification_stdlib.h"

/*@ Extern Coq (fib_mod_z: Z -> Z -> Z) */
/*@ Import Coq Require Import fibonacci_mod */

int fibonacci_mod(int n, int mod)
/*@ Require
      0 <= n &&
      n < 2147483647 &&
      0 < mod &&
      mod <= 1073741824 &&
      emp
    Ensure
      __return == fib_mod_z(n@pre, mod@pre) && emp
*/
{
    int i;
    int a = 0;
    int b = 1 % mod;
    int c;

    if (n == 0) {
        return 0;
    }

    /*@ Inv
          2 <= i && i <= n + 1 &&
          n == n@pre &&
          mod == mod@pre &&
          0 <= a && a < mod &&
          0 <= b && b < mod &&
          a == fib_mod_z(i - 2, mod) &&
          b == fib_mod_z(i - 1, mod) &&
          emp
    */
    for (i = 2; i <= n; ++i) {
        c = (a + b) % mod;
        a = b;
        b = c;
    }

    return b;
}
