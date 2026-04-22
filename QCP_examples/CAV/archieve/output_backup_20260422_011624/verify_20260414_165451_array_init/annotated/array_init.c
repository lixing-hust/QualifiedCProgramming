#include "../../../../verification_stdlib.h"
#include "../../../../verification_list.h"
#include "../../../../int_array_def.h"

void array_init(int n, int *a)
/*@ With l
    Require
      0 <= n && IntArray::full(a, n, l)
    Ensure
      IntArray::full(a, n, zeros(n))
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n@pre && n@pre == Zlength(l) && a == a@pre &&
          IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))
    */
    for (i = 0; i < n; ++i) {
        /*@ 0 <= i && i < n@pre && n@pre == Zlength(l) && a == a@pre &&
              IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))
            which implies
              a == a@pre &&
              IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l))) *
              data_at(a + (i * sizeof(int)), int, l[i])
        */
        a[i] = 0;
        /*@ 0 <= i && i < n@pre && n@pre == Zlength(l) && a == a@pre &&
              IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l))) *
              data_at(a + (i * sizeof(int)), int, 0)
            which implies
              a == a@pre &&
              IntArray::full(a, n@pre, app(zeros(i + 1), sublist(i + 1, n@pre, l)))
        */
    }
}
