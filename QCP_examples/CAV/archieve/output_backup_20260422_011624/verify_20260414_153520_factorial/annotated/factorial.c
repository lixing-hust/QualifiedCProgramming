#include "../../../../verification_stdlib.h"

/*@ Extern Coq (factorial: Z -> Z) */

int fac(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
{
    int i;
    int res = 1;

    /*@ Inv
          1 <= i && i <= n + 1 && n == n@pre && res == factorial(i - 1)
    */
    for (i = 1; i <= n; ++i) {
        /*@ 1 <= i && i <= n@pre && n == n@pre && res == factorial(i - 1) */
        res = res * i;
        /*@ 1 <= i && i <= n@pre && n == n@pre && res == factorial(i) */
    }

    /*@ i == n@pre + 1 && res == factorial(n@pre) */
    return res;
}
