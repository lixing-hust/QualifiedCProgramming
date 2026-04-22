#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void set_zero(int n, int *a)
/*@ With l
    Require
      0 <= n && IntArray::full(a, n, l)
    Ensure
      IntArray::full(a, n, zeros(n))
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        a[i] = 0;
    }
}
