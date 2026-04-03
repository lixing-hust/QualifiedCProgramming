#include "../../verification_stdlib.h"
#include "../../verification_list.h"
/*@ Extern Coq (fib4_coq: Z -> Z) */

int fib4(int n)
/*@ Require
        0 <= n && n < 100 && emp
    Ensure
        __return == fib4_coq(n) && emp
*/
{
    int f[100];
    f[0]=0;
    f[1]=0;
    f[2]=2;
    f[3]=0;
    if (n < 4) return f[n];
    int i;
    /*@ Inv
        4 <= i && i <= n@pre + 1
    */
    for (i=4;i<=n;i++)
    {
        f[i]=f[i-1]+f[i-2]+f[i-3]+f[i-4];
    }
    return f[n];
}
