#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (sorted_z: list Z -> Prop) */
/*@ Import Coq Require Import bubble_sort */

void bubble_sort(int *a, int n)
/*@ With l
    Require
      0 <= n && n <= 2000 &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        sorted_z(l0) &&
        Permutation(l, l0) &&
        IntArray::full(a, n, l0)
*/
{
    int i, j;

    for (i = 0; i < n; ++i) {
        for (j = 0; j + 1 < n - i; ++j) {
            if (a[j] > a[j + 1]) {
                int t = a[j];
                a[j] = a[j + 1];
                a[j + 1] = t;
            }
        }
    }
}
