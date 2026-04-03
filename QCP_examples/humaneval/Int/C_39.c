#include "../verification_stdlib.h"

/*@ Extern Coq (prime_fib_coq: Z -> Z) */

int prime_fib(int n)
/*@ Require
        1 <= n && n < INT_MAX && emp
    Ensure
        __return == prime_fib_coq(n) && emp
*/
{
    int f1, f2, m;
    f1 = 1;
    f2 = 2;
    int count = 0;
    
    /*@ Inv
        0 <= count && count <= n@pre && emp
    */
    while (count < n)
    {
        f1 = f1 + f2;
        m = f1;
        f1 = f2;
        f2 = m;
        
        int isprime = 1;
        int w;
        
        /*@ Inv
            2 <= w && emp
        */
        for (w = 2; w * w <= f1; w++) {
            if (f1 % w == 0) {
                isprime = 0;
                break;
            }
        }
        
        if (isprime) count += 1;
        if (count == n) return f1;
    }
    return 0;
}