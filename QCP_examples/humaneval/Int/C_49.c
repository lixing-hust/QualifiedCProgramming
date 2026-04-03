#include "../../verification_stdlib.h"

/*@ Extern Coq (Zpow: Z -> Z -> Z) */

int modp(int n, int p)
/*@ Require
        0 <= n && p > 0 && emp
    Ensure
        __return == Zpow(2, n) % p && emp
*/
{
    int out=1;
    int i;
    /*@ Inv
        0 <= i && i <= n@pre &&
        out == Zpow(2, i) % p@pre
    */
    for (i=0;i<n;i++)
        out=(out*2)%p;
    return out;
}

