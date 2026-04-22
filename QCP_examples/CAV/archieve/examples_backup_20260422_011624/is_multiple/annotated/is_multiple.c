#include "../../verification_stdlib.h"

int is_multiple(int a, int b)
/*@ Require
      b > 0 && emp
    Ensure
      ((__return == 1 && a@pre % b@pre == 0) ||
       (__return == 0 && a@pre % b@pre != 0)) &&
      emp
*/
{
    if (a % b == 0) {
        return 1;
    }
    return 0;
}
