#include "../../verification_stdlib.h"

/*@ Extern Coq (fib_z: Z -> Z) */
/*@ Import Coq Require Import fibonacci */

int fibonacci(int n)
/*@ Require
      0 <= n && n <= 46 && emp
    Ensure
      __return == fib_z(n@pre) && emp
*/
{
    int i;
    int a = 0;
    int b = 1;
    int c;

    if (n == 0) {
        return 0;
    }

    /*@ Inv
          2 <= i && i <= n + 1 &&
          n == n@pre &&
          a == fib_z(i - 2) &&
          b == fib_z(i - 1) &&
          emp
    */
    for (i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }

    return b;
}
